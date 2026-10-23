use std::collections::HashSet;

use quickscope::ScopeSet;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use smallvec::SmallVec;
use steel_parser::ast::{
    self, parse_lambda, Begin, DEFINE_SYNTAX, QUOTE, SYNTAX_CASE, SYNTAX_RULES,
};
use steel_parser::parser::SourceId;
use steel_parser::tokens::NumberLiteral;

use crate::compiler::modules::RequiredModuleMacros;
use crate::compiler::passes::mangle::collect_defines;
use crate::compiler::program::{BEGIN, LAMBDA, LAMBDA_SYMBOL, LET};
use crate::parser::ast::ExprKind;
use crate::parser::parser::SyntaxObject;
use crate::parser::rename_idents::{resolve_template_bindings, TemplateBindings};
use crate::parser::span_visitor::get_span;
use crate::steel_vm::engine::ModuleContainer;
use crate::{compiler::program::AS_KEYWORD, parser::tokens::TokenType};
use crate::{compiler::program::REQUIRE_BUILTIN, rvals::Result};

use steel_parser::expr_list;
use thin_vec::{thin_vec, ThinVec};

use super::visitors::VisitorMutRef;
use super::{
    ast::{Atom, Define, LambdaFunction, List, Quote},
    interner::InternedString,
    kernel::Kernel,
};

use crate::parser::expander::SteelMacro;

static REST_ARG: &str = "##%list-args";

pub fn extract_macro_defs(
    exprs: &mut Vec<ExprKind>,
    macro_map: &mut FxHashMap<InternedString, SteelMacro>,
    _global_map: &FxHashMap<InternedString, usize>,
) -> Result<()> {
    let mut error = None;

    exprs.retain_mut(|expr| {
        if let ExprKind::Macro(_) = expr {
            // Replace with dummy begin value so we don't have to copy
            // everything other for every macro definition
            let mut taken_expr = ExprKind::Begin(Box::new(Begin::new(
                Vec::new(),
                SyntaxObject::default(TokenType::Begin),
            )));

            core::mem::swap(expr, &mut taken_expr);

            if let ExprKind::Macro(m) = taken_expr {
                match SteelMacro::parse_from_ast_macro(m) {
                    Ok(generated_macro) => {
                        let name = generated_macro.name();
                        macro_map.insert(*name, generated_macro);
                    }
                    Err(e) => {
                        error = Some(e);
                        return false;
                    }
                }
            } else {
                unreachable!();
            }

            return false;
        }

        true
    });

    if let Some(e) = error {
        return Err(e);
    }

    Ok(())
}

#[derive(Copy, Clone, Debug)]
pub enum GlobalMap<'a> {
    Map(&'a FxHashMap<InternedString, usize>),
    Set(&'a FxHashSet<InternedString>),
    // Existing globals plus the definitions collected for the program being compiled.
    Layered(
        &'a FxHashMap<InternedString, usize>,
        &'a FxHashSet<InternedString>,
    ),
    // Expansion-site bindings are separate from a global template's definition-site globals.
    // Lookups see only the expansion-site set; definition-site lookups match on the variant.
    Scoped(&'a GlobalMap<'a>, &'a FxHashSet<InternedString>),
}

impl<'a> GlobalMap<'a> {
    pub fn contains(&self, i: &InternedString) -> bool {
        match self {
            // TODO: Fix this so that we can actually leverage it!
            GlobalMap::Map(_) => false,
            GlobalMap::Set(hash_set) => hash_set.contains(i),
            GlobalMap::Layered(map, set) => map.contains_key(i) || set.contains(i),
            GlobalMap::Scoped(_, set) => set.contains(i),
        }
    }

    pub fn actually_contains(&self, i: &InternedString) -> bool {
        match self {
            // TODO: Fix this so that we can actually leverage it!
            GlobalMap::Map(m) => m.contains_key(i),
            GlobalMap::Set(hash_set) => hash_set.contains(i),
            GlobalMap::Layered(map, set) => map.contains_key(i) || set.contains(i),
            GlobalMap::Scoped(_, set) => set.contains(i),
        }
    }
}

pub fn expand(
    expr: &mut ExprKind,
    map: &FxHashMap<InternedString, SteelMacro>,
    globals: GlobalMap,
) -> Result<ScopeSet<InternedString, FxBuildHasher>> {
    let exclusions = HashSet::new();
    let mut expander = Expander {
        depth: 0,
        map,
        changed: false,
        in_scope_values: ScopeSet::default(),
        source_id: SourceId::none(),
        exclusions: &exclusions,
        globals,
        module_globals: None,
        builtin_modules: None,
        module_scoped: false,
    };
    expander.visit(expr)?;

    Ok(expander.in_scope_values)
}

// Expand a module's own or imported macros. They cannot capture a global template's free
// references, which the global macro expansion resolves at the template's definition site.
pub(crate) fn expand_module_scoped(
    expr: &mut ExprKind,
    map: &FxHashMap<InternedString, SteelMacro>,
    globals: GlobalMap,
) -> Result<()> {
    let exclusions = HashSet::new();
    let mut expander = Expander::new(map, &exclusions, globals);
    expander.module_scoped = true;
    expander.visit(expr)
}

pub fn expand_with_source_id(
    expr: &mut ExprKind,
    map: &FxHashMap<InternedString, SteelMacro>,
    exclusions: &HashSet<InternedString>,
    source_id: Option<SourceId>,
    globals: GlobalMap,
) -> Result<()> {
    let mut expander = Expander {
        depth: 0,
        map,
        changed: false,
        in_scope_values: ScopeSet::default(),
        source_id,
        exclusions,
        globals,
        module_globals: None,
        builtin_modules: None,
        module_scoped: false,
    };

    expander.visit(expr)
}

fn is_let_head(head: &ExprKind) -> bool {
    match head {
        ExprKind::Atom(Atom {
            syn: SyntaxObject {
                ty: TokenType::Let, ..
            },
        }) => true,
        ExprKind::Atom(Atom {
            syn:
                SyntaxObject {
                    ty: TokenType::Identifier(i),
                    ..
                },
        }) => *i == *LET,
        _ => false,
    }
}

pub(crate) fn is_begin_head(head: &ExprKind) -> bool {
    head.atom_identifier() == Some(&*BEGIN)
        || head
            .atom_syntax_object()
            .is_some_and(|syntax| syntax.ty == TokenType::Begin)
}

// Bind a parameter list in the current layer. Defaults run before optional and keyword bindings
// are introduced, so they see only the positional parameters ahead of them.
fn visit_parameters<V: VisitorMutRef<Output = Result<()>>>(
    visitor: &mut V,
    scope: fn(&mut V) -> &mut ScopeSet<InternedString, FxBuildHasher>,
    args: &mut [ExprKind],
) -> Result<()> {
    let positional_count = args
        .iter()
        .take_while(|arg| arg.atom_identifier().is_some())
        .count();
    for arg in &args[..positional_count] {
        scope(visitor).define(*arg.atom_identifier().unwrap());
    }
    for arg in &mut args[positional_count..] {
        if let ExprKind::List(binding) = arg {
            if let Some(default) = binding.args.get_mut(1) {
                visitor.visit(default)?;
            }
        }
    }
    for arg in &args[positional_count..] {
        if let Some(ident) = arg
            .atom_identifier()
            .or_else(|| arg.list().and_then(List::first_ident))
        {
            scope(visitor).define(*ident);
        }
    }
    Ok(())
}

fn visit_let_form<V: VisitorMutRef<Output = Result<()>>>(
    visitor: &mut V,
    scope: fn(&mut V) -> &mut ScopeSet<InternedString, FxBuildHasher>,
    l: &mut List,
    visit_body: impl FnOnce(&mut V, &mut [ExprKind]) -> Result<()>,
) -> Result<()> {
    let name = l.args.get(1).and_then(|x| x.atom_identifier()).copied();
    let bindings_index = if name.is_some() { 2 } else { 1 };

    scope(visitor).push_layer();

    if let Some(name) = name {
        scope(visitor).define(name);
    }

    if let Some(ExprKind::List(bindings)) = l.args.get_mut(bindings_index) {
        for arg in &mut bindings.args {
            if let ExprKind::List(binding) = arg {
                if let Some(ident) = binding.first_ident() {
                    scope(visitor).define(*ident);
                }

                if let Some(expr) = binding.args.get_mut(0) {
                    visitor.visit(expr)?;
                }

                if let Some(expr) = binding.args.get_mut(1) {
                    visitor.visit(expr)?;
                }
            }
        }
    }

    if let Some(body_args) = l.args.get_mut(bindings_index + 1..) {
        visit_body(visitor, body_args)?;
    }

    scope(visitor).pop_layer();

    Ok(())
}

// HACK: template identifiers that collide with a local get renamed to `##name`. If that
// identifier was a reference to a macro, put the original name back so that things
// behave
fn restore_hygienic_macro_head(
    l: &mut List,
    in_scope: &ScopeSet<InternedString, FxBuildHasher>,
    is_macro: impl Fn(&InternedString) -> bool,
) {
    if let Some(ExprKind::Atom(Atom {
        syn:
            SyntaxObject {
                ty: TokenType::Identifier(s),
                unresolved: true,
                ..
            },
    })) = l.args.first_mut()
    {
        if in_scope.contains(s) || is_macro(s) {
            return;
        }

        if let Some(original) = s.resolve().strip_prefix("##") {
            let original: InternedString = original.into();

            if is_macro(&original) {
                *s = original;
            }
        }
    }
}

pub struct Expander<'a> {
    map: &'a FxHashMap<InternedString, SteelMacro>,
    exclusions: &'a HashSet<InternedString>,
    globals: GlobalMap<'a>,
    module_globals: Option<&'a FxHashSet<InternedString>>,
    builtin_modules: Option<&'a ModuleContainer>,
    // Expands a module's own or imported macros, which never claim global template references.
    module_scoped: bool,
    pub(crate) changed: bool,
    // We're going to actually check if the macro is in scope
    in_scope_values: ScopeSet<InternedString, FxBuildHasher>,
    source_id: Option<SourceId>,
    depth: usize,
}

#[derive(Debug)]
pub struct RequiredMacroMap<'a> {
    pub(crate) map: &'a mut RequiredModuleMacros,
    pub(crate) changed: bool,
}

pub struct ExpanderMany<'a> {
    // Base map, but then also we want to include _all_
    pub(crate) map: &'a mut FxHashMap<InternedString, SteelMacro>,

    pub(crate) overlays: Vec<RequiredMacroMap<'a>>,

    // We're going to actually check if the macro is in scope
    pub(crate) in_scope_values: ScopeSet<InternedString, FxBuildHasher>,

    pub(crate) globals: GlobalMap<'a>,
    source_id: Option<SourceId>,
    depth: usize,
}

impl<'a> ExpanderMany<'a> {
    pub fn new(
        map: &'a mut FxHashMap<InternedString, SteelMacro>,
        overlays: Vec<RequiredMacroMap<'a>>,
        globals: GlobalMap<'a>,
    ) -> Self {
        Self {
            map,
            overlays,
            in_scope_values: ScopeSet::default(),
            source_id: SourceId::none(),
            globals,
            depth: 0,
        }
    }

    pub fn expand(&mut self, expr: &mut ExprKind) -> Result<()> {
        self.visit(expr)?;

        // This isn't good! this is quadratic
        for i in self.in_scope_values.iter() {
            self.map.remove(i);
        }

        self.in_scope_values.clear_all();
        Ok(())
    }

    // Expand a statement while keeping the bindings of the statements before it in scope. Only
    // this statement's definitions can newly shadow a macro, so scanning every binding in scope
    // would make a module's expansion quadratic.
    pub(crate) fn expand_in_scope(&mut self, expr: &mut ExprKind) -> Result<()> {
        self.visit(expr)?;
        collect_defines(std::slice::from_ref(expr), &mut |name| {
            self.map.remove(&name);
        });
        Ok(())
    }

    // An unresolved global macro can change later native heads, so defer their bodies while
    // still discovering definitions introduced by module macros. A macro named by one of the
    // `shadowed` top-level definitions is left for the deferred pass to resolve, and the
    // definitions found here, including those earlier in the same `begin`, are added to it.
    pub(crate) fn expand_top_level(
        &mut self,
        expr: &mut ExprKind,
        shadowed: &mut FxHashSet<InternedString>,
    ) -> Result<()> {
        match expr {
            ExprKind::Begin(begin) => begin
                .exprs
                .iter_mut()
                .try_for_each(|expr| self.expand_top_level(expr, shadowed)),
            ExprKind::List(list) if list.first().is_some_and(is_begin_head) => list.args[1..]
                .iter_mut()
                .try_for_each(|expr| self.expand_top_level(expr, shadowed)),
            ExprKind::List(list)
                if list.first_ident().is_some_and(|name| {
                    !shadowed.contains(name)
                        && (self.map.contains_key(name)
                            || self
                                .overlays
                                .iter()
                                .any(|overlay| overlay.map.in_scope_macros.contains_key(name)))
                }) =>
            {
                self.expand(expr)?;
                // Only this expansion may name an imported module's private macros. The rest of
                // the statement has not seen this module's own macros yet, so it must not be
                // exposed to them.
                for overlay in &mut self.overlays {
                    if overlay.changed {
                        expand_module_scoped(expr, &overlay.map.module_macros, self.globals)?;
                        overlay.changed = false;
                    }
                }
                collect_defines(std::slice::from_ref(expr), &mut |name| {
                    shadowed.insert(name);
                });
                Ok(())
            }
            _ => {
                collect_defines(std::slice::from_ref(expr), &mut |name| {
                    shadowed.insert(name);
                });
                Ok(())
            }
        }
    }
}

impl<'a> Expander<'a> {
    pub fn new(
        map: &'a FxHashMap<InternedString, SteelMacro>,
        exclusions: &'a HashSet<InternedString>,
        globals: GlobalMap<'a>,
    ) -> Self {
        Self {
            map,
            changed: false,
            in_scope_values: ScopeSet::default(),
            source_id: SourceId::none(),
            depth: 0,
            exclusions,
            globals,
            module_globals: None,
            builtin_modules: None,
            module_scoped: false,
        }
    }

    pub fn expand(&mut self, expr: &mut ExprKind) -> Result<()> {
        self.visit(expr)
    }

    pub(crate) fn expand_global_macros(
        expr: &mut ExprKind,
        map: &'a FxHashMap<InternedString, SteelMacro>,
        global_bindings: GlobalMap<'a>,
        module_globals: &'a mut FxHashSet<InternedString>,
        builtin_modules: &'a ModuleContainer,
    ) -> Result<()> {
        if map.is_empty() {
            return Ok(());
        }
        collect_defines(std::slice::from_ref(expr), &mut |name| {
            module_globals.insert(name);
        });
        let exclusions = HashSet::new();
        let mut expander = Expander::new(
            map,
            &exclusions,
            GlobalMap::Scoped(&global_bindings, module_globals),
        );
        expander.module_globals = Some(module_globals);
        expander.builtin_modules = Some(builtin_modules);
        expander.expand(expr)
    }

    fn excluded(&self, name: &InternedString) -> bool {
        self.exclusions.contains(name)
            || self
                .module_globals
                .is_some_and(|globals| globals.contains(name))
    }

    // A nested macro can bind a global template's free reference as a parameter, which then names
    // that parameter within its scope rather than a global binding. Only global macro expansion
    // classifies free references, so other expansions have nothing to resolve.
    fn template_parameters<'p>(
        &self,
        parameters: impl Iterator<Item = &'p ExprKind>,
    ) -> Option<TemplateBindings> {
        self.module_globals?;
        let mut bindings = TemplateBindings::default();
        parameters.for_each(|parameter| bindings.bind_parameter(parameter));
        Some(bindings)
    }

    fn visit_body(&mut self, exprs: &mut [ExprKind]) -> Result<()> {
        if self.module_globals.is_none() {
            return exprs.iter_mut().try_for_each(|expr| self.visit(expr));
        }
        // Bodies see later definitions, but statement heads retain their sequential scope.
        let mut heads = self.in_scope_values.clone();
        predeclare_native_definitions(
            exprs,
            &|name| heads.contains(name),
            self.globals,
            &|name| self.map.contains_key(name),
            self.builtin_modules,
            &mut |name| self.in_scope_values.define(name),
        );
        self.visit_body_with_native_heads(exprs, &mut heads)
    }

    fn visit_body_with_native_heads(
        &mut self,
        exprs: &mut [ExprKind],
        heads: &mut ScopeSet<InternedString, FxBuildHasher>,
    ) -> Result<()> {
        let mut prepared = 0;
        for index in 0..exprs.len() {
            if index >= prepared {
                let (_, count) =
                    lower_native_definitions(&mut exprs[index..], self.globals, heads, &|name| {
                        self.map.contains_key(name)
                    })?;
                prepared = index + count;
                collect_defines(&exprs[index..prepared], &mut |name| {
                    self.in_scope_values.define(name);
                });
            }
            self.visit_with_native_heads(&mut exprs[index], Some(heads))?;
            resolve_template_bindings(exprs, index);
            collect_defines(std::slice::from_ref(&exprs[index]), &mut |name| {
                heads.define(name);
            });
        }
        Ok(())
    }

    fn visit_with_native_heads(
        &mut self,
        expr: &mut ExprKind,
        native_heads: Option<&mut ScopeSet<InternedString, FxBuildHasher>>,
    ) -> Result<()> {
        if self.depth > 512 {
            stop!(Generic => "macro expansion depth reached!");
        }

        match expr {
            ExprKind::If(f) => self.visit_if(f),
            ExprKind::Define(d) => self.visit_define(d),
            ExprKind::LambdaFunction(l) => self.visit_lambda_function(l),
            ExprKind::Begin(b) => match native_heads {
                Some(heads) => self.visit_body_with_native_heads(&mut b.exprs, heads),
                None => self.visit_begin(b),
            },
            ExprKind::Return(r) => self.visit_return(r),
            ExprKind::Let(l) => self.visit_let(l),
            ExprKind::Quote(q) => self.visit_quote(q),
            ExprKind::Macro(m) => self.visit_macro(m),
            ExprKind::Atom(a) => self.visit_atom(a),
            ExprKind::List(l) => {
                restore_hygienic_macro_head(l, &self.in_scope_values, |name| {
                    self.map.contains_key(name) && !self.excluded(name)
                });

                if self.module_globals.is_some() {
                    if !l
                        .first_ident()
                        .is_some_and(|name| self.map.contains_key(name))
                    {
                        if let Some(lowered) = lower_native_form(l, self.globals, |name| {
                            native_heads
                                .as_deref()
                                .unwrap_or(&self.in_scope_values)
                                .contains(name)
                        })? {
                            *expr = lowered;
                            return self.visit_with_native_heads(expr, native_heads);
                        }
                    }
                    if l.first().is_some_and(is_begin_head) {
                        return match native_heads {
                            Some(heads) => {
                                self.visit_body_with_native_heads(&mut l.args[1..], heads)
                            }
                            None => self.visit_body(&mut l.args[1..]),
                        };
                    }
                }

                match l.first() {
                    // TODO: Come back to this?
                    Some(ExprKind::Atom(
                        ident @ Atom {
                            syn:
                                SyntaxObject {
                                    ty: TokenType::Identifier(s),
                                    ..
                                },
                        },
                    )) if *s == *LAMBDA_SYMBOL || *s == *LAMBDA => {
                        if let ExprKind::LambdaFunction(mut lambda) =
                            parse_lambda(ident.clone(), l.args.clone())?
                        {
                            self.visit_lambda_function(&mut lambda)?;

                            *expr = ExprKind::LambdaFunction(lambda);

                            return Ok(());

                            // return self.visit_lambda_function(&mut lambda);

                            // return self.visit_lambda_function(lambda);
                        } else {
                            unreachable!()
                        }
                    }
                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Quote,
                                ..
                            },
                    })) => return Ok(()),

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(i),
                                ..
                            },
                    })) if *i == *QUOTE => return Ok(()),

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(i),
                                ..
                            },
                    })) if *i == *SYNTAX_CASE && !self.in_scope_values.contains(i) => {
                        if let Some(args) = l.args.get_mut(3..) {
                            for arg in args {
                                if let ExprKind::List(l) = arg {
                                    if let Some(rest) = l.args.get_mut(1..) {
                                        for arg in rest {
                                            self.visit(arg)?;
                                        }
                                    }
                                } else {
                                    self.visit(arg)?;
                                }
                            }
                        }
                        return Ok(());
                    }

                    Some(head) if is_let_head(head) => {
                        let named = l.args.get(1).and_then(ExprKind::atom_identifier).is_some();
                        let bindings_index = if named { 2 } else { 1 };
                        let bindings = match l.args.get(bindings_index) {
                            Some(ExprKind::List(bindings)) => bindings.args.as_slice(),
                            _ => &[],
                        };
                        if let Some(mut parameters) = self
                            .template_parameters(l.args[1..bindings_index].iter().chain(bindings))
                        {
                            // Binding values are outside the scope of the names they bind.
                            if named {
                                parameters.resolve(&mut l.args[1]);
                            }
                            if let Some(ExprKind::List(bindings)) = l.args.get_mut(bindings_index) {
                                for binding in &mut bindings.args {
                                    match binding {
                                        ExprKind::List(binding) => {
                                            if let Some(name) = binding.args.first_mut() {
                                                parameters.resolve(name);
                                            }
                                        }
                                        binding => parameters.resolve(binding),
                                    }
                                }
                            }
                            for expr in l.args.iter_mut().skip(bindings_index + 1) {
                                parameters.resolve(expr);
                            }
                        }
                        return visit_let_form(
                            self,
                            |v| &mut v.in_scope_values,
                            l,
                            Self::visit_body,
                        );
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(i),
                                ..
                            },
                    })) if *i == *SYNTAX_RULES && !self.in_scope_values.contains(i) => {
                        if let Some(args) = l.args.get_mut(2..) {
                            for arg in args {
                                self.visit(arg)?;
                            }
                        }
                        return Ok(());
                    }
                    // If we're in define-syntax, don't expand the list of the name
                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(i),
                                ..
                            },
                    })) if *i == *DEFINE_SYNTAX && !self.in_scope_values.contains(i) => {
                        if let Some(arg) = l.args.get_mut(2) {
                            self.visit(arg)?;
                        }
                        return Ok(());
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::DefineSyntax,
                                ..
                            },
                    })) if !self.in_scope_values.contains(&DEFINE_SYNTAX) => {
                        if let Some(arg) = l.args.get_mut(2) {
                            self.visit(arg)?;
                        }

                        return Ok(());
                    }

                    Some(ExprKind::Atom(
                        ident @ Atom {
                            syn:
                                SyntaxObject {
                                    ty: TokenType::Lambda,
                                    ..
                                },
                        },
                    )) => {
                        if let ExprKind::LambdaFunction(mut lambda) =
                            parse_lambda(ident.clone(), core::mem::take(&mut l.args))?
                        {
                            if l.improper {
                                lambda.rest = true;
                            }

                            self.visit_lambda_function(&mut lambda)?;

                            *expr = ExprKind::LambdaFunction(lambda);

                            return Ok(());
                        } else {
                            unreachable!()
                        }
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Define,
                                ..
                            },
                    })) => {
                        // self.in_scope_values.define(key);
                        // todo!()

                        // println!("Getting here: {}", l);

                        if l.args.len() == 1 {
                            stop!(BadSyntax => "define has neither head nor body"; l.location);
                        }

                        let is_function = match &l.args[1] {
                            ExprKind::List(l) if l.first_ident().is_some() => {
                                self.in_scope_values.define(*l.first_ident().unwrap());
                                true
                            }

                            ExprKind::Atom(a) if a.ident().is_some() => {
                                self.in_scope_values.define(*a.ident().unwrap());
                                false
                            }
                            _ => false,
                        };

                        if is_function {
                            if let ExprKind::List(signature) = &l.args[1] {
                                if let Some(mut parameters) =
                                    self.template_parameters(signature.args[1..].iter())
                                {
                                    l.args[1..]
                                        .iter_mut()
                                        .for_each(|expr| parameters.resolve(expr));
                                }
                            }

                            self.in_scope_values.push_layer();

                            if let ExprKind::List(signature) = &mut l.args[1] {
                                visit_parameters(
                                    self,
                                    |v| &mut v.in_scope_values,
                                    &mut signature.args[1..],
                                )?;
                            }
                        }

                        self.visit_body(&mut l.args[2..])?;

                        if is_function {
                            self.in_scope_values.pop_layer();
                        }

                        return Ok(());
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(s),
                                span: sp,
                                unresolved,
                                global_reference,
                                ..
                            },
                    })) => {
                        // Interweave the macro expansion
                        if let Some(m) = self.map.get(s) {
                            // A global template's free reference names a global binding, so a
                            // module's own or imported macros cannot claim it, while the global
                            // macro expansion resolves it past any local binding of the name.
                            // Top-level definitions in `exclusions` still shadow it.
                            // Substituting it through a pattern variable clears `unresolved`.
                            let applies = if *global_reference {
                                !self.module_scoped && !self.exclusions.contains(s)
                            } else {
                                !self.excluded(s)
                            };
                            let global_template_reference =
                                *global_reference && self.module_globals.is_some();
                            if applies {
                                // If this macro has been overwritten by any local value, respect
                                // the local binding and do not expand the macro, unless the
                                // identifier came from a macro template
                                let visible = self.source_id.is_none()
                                    || sp.source_id() == m.location.source_id();

                                if global_template_reference
                                    || *unresolved
                                    || visible && !self.in_scope_values.contains(s)
                                {
                                    let span = *sp;

                                    let mut expanded = m.expand_with_global_scope(
                                        List::new_maybe_improper(
                                            core::mem::take(&mut l.args),
                                            l.improper,
                                        ),
                                        span,
                                        &self.in_scope_values,
                                        self.module_globals
                                            .map(GlobalMap::Set)
                                            .unwrap_or(self.globals),
                                        self.builtin_modules
                                            .map(|modules| (self.map, modules, self.globals)),
                                    )?;
                                    self.changed = true;

                                    self.depth += 1;

                                    resolve_template_bindings(
                                        std::slice::from_mut(&mut expanded),
                                        0,
                                    );
                                    self.visit_with_native_heads(&mut expanded, native_heads)?;

                                    self.depth -= 1;

                                    *expr = expanded;

                                    return Ok(());
                                }
                            }

                            // let expanded = m.expand(l.clone(), *sp)?;
                            // self.changed = true;
                            // return self.visit(expanded);
                        }
                        if *s == *REQUIRE_BUILTIN {
                            if let Some(builtin_modules) = self.builtin_modules {
                                *expr = expand_require_builtin(&l.args[1..], builtin_modules)?;
                                collect_defines(std::slice::from_ref(expr), &mut |name| {
                                    self.in_scope_values.define(name);
                                });
                                return Ok(());
                            }
                        }
                    }
                    // Some(other) => {
                    //     println!("543 - DIDN'T MATCH: {}", other);
                    //     // println!("{:?}", other);
                    // }
                    _ => {}
                }

                for expr in l.args.iter_mut() {
                    self.visit(expr)?;
                }

                Ok(())

                // l.args = l
                //     .args
                //     .into_iter()
                //     .map(|e| self.visit(e))
                //     .collect::<Result<Vec<_>>>()?;
            }
            ExprKind::SyntaxRules(s) => self.visit_syntax_rules(s),
            ExprKind::Set(s) => self.visit_set(s),
            ExprKind::Require(r) => self.visit_require(r),
            ExprKind::Vector(v) => self.visit_vector(v),
        }
    }
}

impl<'a> VisitorMutRef for Expander<'a> {
    type Output = Result<()>;

    fn visit(&mut self, expr: &mut ExprKind) -> Self::Output {
        self.visit_with_native_heads(expr, None)
    }

    fn visit_if(&mut self, f: &mut super::ast::If) -> Self::Output {
        self.visit(&mut f.test_expr)?;
        self.visit(&mut f.then_expr)?;
        self.visit(&mut f.else_expr)?;
        Ok(())
    }

    fn visit_define(&mut self, define: &mut super::ast::Define) -> Self::Output {
        if let Some(ident) = define.name.atom_identifier() {
            self.in_scope_values.define(*ident);
        }

        self.visit(&mut define.body)?;
        Ok(())
    }

    fn visit_lambda_function(
        &mut self,
        lambda_function: &mut super::ast::LambdaFunction,
    ) -> Self::Output {
        if let Some(mut parameters) = self.template_parameters(lambda_function.args.iter()) {
            lambda_function
                .args
                .iter_mut()
                .chain(std::iter::once(&mut lambda_function.body))
                .for_each(|expr| parameters.resolve(expr));
        }

        self.in_scope_values.push_layer();

        visit_parameters(self, |v| &mut v.in_scope_values, &mut lambda_function.args)?;
        self.visit_body(std::slice::from_mut(&mut lambda_function.body))?;

        self.in_scope_values.pop_layer();

        Ok(())
    }

    fn visit_begin(&mut self, begin: &mut super::ast::Begin) -> Self::Output {
        self.visit_body(&mut begin.exprs)
    }

    fn visit_return(&mut self, r: &mut super::ast::Return) -> Self::Output {
        self.visit(&mut r.expr)
    }

    fn visit_quote(&mut self, _quote: &mut super::ast::Quote) -> Self::Output {
        // println!("Visiting quote with : {:?}", quote);
        // quote.expr = self.visit(quote.expr)?;
        // Ok(ExprKind::Quote(quote))
        Ok(())
    }

    fn visit_macro(&mut self, m: &mut super::ast::Macro) -> Self::Output {
        stop!(BadSyntax => format!("unexpected macro definition in expand visitor: {}", m); m.location.span)
    }

    fn visit_atom(&mut self, _a: &mut Atom) -> Self::Output {
        // Ok(ExprKind::Atom(a))
        Ok(())
    }

    fn visit_syntax_rules(&mut self, l: &mut super::ast::SyntaxRules) -> Self::Output {
        stop!(Generic => "unexpected syntax-rules definition"; l.location.span)
    }

    fn visit_set(&mut self, s: &mut super::ast::Set) -> Self::Output {
        self.visit(&mut s.variable)?;
        self.visit(&mut s.expr)?;
        Ok(())
    }

    fn visit_require(&mut self, _s: &mut super::ast::Require) -> Self::Output {
        // Ok(ExprKind::Require(s))
        Ok(())
    }

    fn visit_let(&mut self, l: &mut super::ast::Let) -> Self::Output {
        if let Some(mut parameters) =
            self.template_parameters(l.bindings.iter().map(|(binding, _)| binding))
        {
            l.bindings
                .iter_mut()
                .map(|(binding, _)| binding)
                .chain(std::iter::once(&mut l.body_expr))
                .for_each(|expr| parameters.resolve(expr));
        }

        self.in_scope_values.push_layer();

        for (binding, _) in l.bindings.iter_mut() {
            if let Some(ident) = binding.atom_identifier() {
                self.in_scope_values.define(*ident);
            }
        }

        for (binding, expr) in l.bindings.iter_mut() {
            self.visit(binding)?;
            self.visit(expr)?;
        }

        self.visit_body(std::slice::from_mut(&mut l.body_expr))?;

        self.in_scope_values.pop_layer();

        Ok(())
    }

    fn visit_list(&mut self, _l: &mut List) -> Self::Output {
        Ok(())
    }

    fn visit_vector(&mut self, _v: &mut super::ast::Vector) -> Self::Output {
        Ok(())
    }
}

impl<'a> VisitorMutRef for ExpanderMany<'a> {
    type Output = Result<()>;

    fn visit(&mut self, expr: &mut ExprKind) -> Self::Output {
        // println!("expanding: {:?}", expr);

        if self.depth > 512 {
            stop!(Generic => "macro expansion depth reached!");
        }

        match expr {
            ExprKind::If(f) => self.visit_if(f),
            ExprKind::Define(d) => self.visit_define(d),
            ExprKind::LambdaFunction(l) => self.visit_lambda_function(l),
            ExprKind::Begin(b) => self.visit_begin(b),
            ExprKind::Return(r) => self.visit_return(r),
            ExprKind::Let(l) => self.visit_let(l),
            ExprKind::Quote(q) => self.visit_quote(q),
            ExprKind::Macro(m) => self.visit_macro(m),
            ExprKind::Atom(a) => self.visit_atom(a),
            ExprKind::List(l) => {
                restore_hygienic_macro_head(l, &self.in_scope_values, |name| {
                    self.overlays
                        .iter()
                        .any(|x| x.map.in_scope_macros.contains_key(name))
                        || self.map.contains_key(name)
                });

                match l.first() {
                    // TODO: Come back to this?
                    Some(ExprKind::Atom(
                        ident @ Atom {
                            syn:
                                SyntaxObject {
                                    ty: TokenType::Identifier(s),
                                    ..
                                },
                        },
                    )) if *s == *LAMBDA_SYMBOL || *s == *LAMBDA => {
                        if let ExprKind::LambdaFunction(mut lambda) =
                            parse_lambda(ident.clone(), l.args.clone())?
                        {
                            self.visit_lambda_function(&mut lambda)?;

                            *expr = ExprKind::LambdaFunction(lambda);

                            return Ok(());

                            // return self.visit_lambda_function(&mut lambda);

                            // return self.visit_lambda_function(lambda);
                        } else {
                            unreachable!()
                        }
                    }
                    Some(head) if is_let_head(head) => {
                        return visit_let_form(
                            self,
                            |v| &mut v.in_scope_values,
                            l,
                            |v, body| body.iter_mut().try_for_each(|expr| v.visit(expr)),
                        );
                    }
                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Quote,
                                ..
                            },
                    })) => return Ok(()),

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(i),
                                ..
                            },
                    })) if *i == *QUOTE => return Ok(()),
                    Some(ExprKind::Atom(
                        ident @ Atom {
                            syn:
                                SyntaxObject {
                                    ty: TokenType::Lambda,
                                    ..
                                },
                        },
                    )) => {
                        if let ExprKind::LambdaFunction(mut lambda) =
                            parse_lambda(ident.clone(), core::mem::take(&mut l.args))?
                        {
                            if l.improper {
                                lambda.rest = true;
                            }

                            self.visit_lambda_function(&mut lambda)?;

                            *expr = ExprKind::LambdaFunction(lambda);

                            return Ok(());

                            // return self.visit_lambda_function(&mut lambda);
                        } else {
                            unreachable!()
                        }
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(i),
                                ..
                            },
                    })) if *i == *DEFINE_SYNTAX && !self.in_scope_values.contains(i) => {
                        if let Some(arg) = l.args.get_mut(2) {
                            self.visit(arg)?;
                        }
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::DefineSyntax,
                                ..
                            },
                    })) if !self.in_scope_values.contains(&DEFINE_SYNTAX) => {
                        if let Some(arg) = l.args.get_mut(2) {
                            self.visit(arg)?;
                        }
                    }

                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Define,
                                ..
                            },
                    })) => {
                        // self.in_scope_values.define(key);
                        // todo!()

                        // println!("Getting here: {}", l);

                        if l.args.len() == 1 {
                            stop!(BadSyntax => "define has neither head nor body"; l.location);
                        }

                        let is_function = match &l.args[1] {
                            ExprKind::List(l) if l.first_ident().is_some() => {
                                self.in_scope_values.define(*l.first_ident().unwrap());
                                true
                            }

                            ExprKind::Atom(a) if a.ident().is_some() => {
                                self.in_scope_values.define(*a.ident().unwrap());
                                false
                            }
                            _ => false,
                        };

                        if is_function {
                            self.in_scope_values.push_layer();

                            if let ExprKind::List(signature) = &mut l.args[1] {
                                visit_parameters(
                                    self,
                                    |v| &mut v.in_scope_values,
                                    &mut signature.args[1..],
                                )?;
                            }
                        }

                        for expr in l.args[2..].iter_mut() {
                            self.visit(expr)?;
                        }

                        if is_function {
                            self.in_scope_values.pop_layer();
                        }

                        return Ok(());
                    }

                    // A global template's free reference cannot name a module's own or imported
                    // macro.
                    Some(ExprKind::Atom(Atom {
                        syn:
                            SyntaxObject {
                                ty: TokenType::Identifier(s),
                                span: sp,
                                unresolved,
                                global_reference: false,
                                ..
                            },
                    })) => {
                        let mut found_index = None;

                        // Interweave the macro expansion
                        if let Some(m) = self
                            .overlays
                            .iter()
                            .enumerate()
                            .find_map(|(index, x)| {
                                let res = x.map.in_scope_macros.get(s);
                                if res.is_some() {
                                    found_index = Some(index);
                                }

                                res
                            })
                            .or_else(|| self.map.get(s))
                        {
                            // If this macro has been overwritten by any local value, respect
                            // the local binding and do not expand the macro, unless the
                            // identifier came from a macro template
                            let visible = self.source_id.is_none()
                                || self.source_id == m.location.source_id();

                            if *unresolved || visible && !self.in_scope_values.contains(s) {
                                // if s.resolve().ends_with("skip-compile") {
                                //     println!("Expanding skip compile: {}", l);
                                // }

                                let span = *sp;

                                // println!("Expanding many: {}", l);

                                let mut expanded = m.expand(
                                    List::new_maybe_improper(
                                        core::mem::take(&mut l.args),
                                        l.improper,
                                    ),
                                    span,
                                    &self.in_scope_values,
                                    self.globals,
                                )?;

                                if let Some(index) = found_index {
                                    self.overlays[index].changed = true;
                                }

                                self.depth += 1;

                                self.visit(&mut expanded)?;

                                self.depth -= 1;

                                *expr = expanded;

                                return Ok(());
                            }

                            // let expanded = m.expand(l.clone(), *sp)?;
                            // self.changed = true;
                            // return self.visit(expanded);
                        }
                    }
                    // Some(other) => {
                    //     println!("967 - DIDN'T MATCH: {}", other)
                    // }
                    _ => {}
                }

                for expr in l.args.iter_mut() {
                    self.visit(expr)?;
                }

                Ok(())

                // l.args = l
                //     .args
                //     .into_iter()
                //     .map(|e| self.visit(e))
                //     .collect::<Result<Vec<_>>>()?;
            }
            ExprKind::SyntaxRules(s) => self.visit_syntax_rules(s),
            ExprKind::Set(s) => self.visit_set(s),
            ExprKind::Require(r) => self.visit_require(r),
            ExprKind::Vector(v) => self.visit_vector(v),
        }
    }

    fn visit_if(&mut self, f: &mut super::ast::If) -> Self::Output {
        self.visit(&mut f.test_expr)?;
        self.visit(&mut f.then_expr)?;
        self.visit(&mut f.else_expr)?;
        Ok(())
    }

    fn visit_define(&mut self, define: &mut super::ast::Define) -> Self::Output {
        if let Some(ident) = define.name.atom_identifier() {
            self.in_scope_values.define(*ident);
        }

        self.visit(&mut define.body)?;
        Ok(())
    }

    fn visit_lambda_function(
        &mut self,
        lambda_function: &mut super::ast::LambdaFunction,
    ) -> Self::Output {
        self.in_scope_values.push_layer();

        visit_parameters(self, |v| &mut v.in_scope_values, &mut lambda_function.args)?;

        self.visit(&mut lambda_function.body)?;

        self.in_scope_values.pop_layer();

        Ok(())
    }

    fn visit_begin(&mut self, begin: &mut super::ast::Begin) -> Self::Output {
        for expr in begin.exprs.iter_mut() {
            self.visit(expr)?;
        }

        Ok(())
    }

    fn visit_return(&mut self, r: &mut super::ast::Return) -> Self::Output {
        self.visit(&mut r.expr)
    }

    fn visit_quote(&mut self, _quote: &mut super::ast::Quote) -> Self::Output {
        // println!("Visiting quote with : {:?}", quote);
        // quote.expr = self.visit(quote.expr)?;
        // Ok(ExprKind::Quote(quote))
        Ok(())
    }

    fn visit_macro(&mut self, m: &mut super::ast::Macro) -> Self::Output {
        stop!(BadSyntax => format!("unexpected macro definition in expand visitor: {}", m); m.location.span)
    }

    fn visit_atom(&mut self, _a: &mut Atom) -> Self::Output {
        // Ok(ExprKind::Atom(a))
        Ok(())
    }

    fn visit_syntax_rules(&mut self, l: &mut super::ast::SyntaxRules) -> Self::Output {
        stop!(Generic => "unexpected syntax-rules definition"; l.location.span)
    }

    fn visit_set(&mut self, s: &mut super::ast::Set) -> Self::Output {
        self.visit(&mut s.variable)?;
        self.visit(&mut s.expr)?;
        Ok(())
    }

    fn visit_require(&mut self, _s: &mut super::ast::Require) -> Self::Output {
        // Ok(ExprKind::Require(s))
        Ok(())
    }

    fn visit_let(&mut self, l: &mut super::ast::Let) -> Self::Output {
        self.in_scope_values.push_layer();

        for (binding, _) in l.bindings.iter_mut() {
            if let Some(ident) = binding.atom_identifier() {
                self.in_scope_values.define(*ident);
            }
        }

        for (binding, expr) in l.bindings.iter_mut() {
            self.visit(binding)?;
            self.visit(expr)?;
        }

        self.visit(&mut l.body_expr)?;

        self.in_scope_values.pop_layer();

        Ok(())
    }

    fn visit_list(&mut self, _l: &mut List) -> Self::Output {
        Ok(())
    }

    fn visit_vector(&mut self, _v: &mut super::ast::Vector) -> Self::Output {
        Ok(())
    }
}

pub fn expand_kernel_in_env_with_allowed(
    mut expr: ExprKind,
    kernel: Option<&mut Kernel>,
    builtin_modules: ModuleContainer,
    env: &str,
    allowed: &FxHashSet<InternedString>,
    globals: GlobalMap,
) -> Result<(ExprKind, bool)> {
    let mut expander = KernelExpander {
        map: kernel,
        changed: false,
        builtin_modules,
        environment: Some(env),
        depth: 0,
        allowed_macros: Some(allowed),
        define_context: None,
        in_scope_values: ScopeSet::default(),
        globals,
    };

    expander.visit(&mut expr)?;

    Ok((expr, expander.changed))

    // expander.visit(expr).map(|x| (x, expander.changed))
}

pub fn expand_kernel_in_env_with_change(
    expr: &mut ExprKind,
    kernel: Option<&mut Kernel>,
    builtin_modules: ModuleContainer,
    env: &str,
    globals: GlobalMap,
) -> Result<bool> {
    let mut expander = KernelExpander {
        map: kernel,
        changed: false,
        builtin_modules,
        environment: Some(env),
        depth: 0,
        allowed_macros: None,
        define_context: None,
        in_scope_values: ScopeSet::default(),
        globals,
    };

    // TODO: Set the environment during loading here
    //

    expander.visit(expr)?;

    Ok(expander.changed)

    // Ok((expr, expander.changed))
}

pub fn expand_kernel_in_env(
    expr: &mut ExprKind,
    kernel: Option<&mut Kernel>,
    builtin_modules: ModuleContainer,
    env: &str,
    globals: GlobalMap,
) -> Result<()> {
    let mut expander = KernelExpander {
        map: kernel,
        changed: false,
        builtin_modules,
        environment: Some(env),
        depth: 0,
        allowed_macros: None,
        define_context: None,
        in_scope_values: ScopeSet::default(),
        globals,
    };

    expander.visit(expr)
}

pub fn expand_kernel(
    mut expr: ExprKind,
    kernel: Option<&mut Kernel>,
    builtin_modules: ModuleContainer,
    globals: GlobalMap,
) -> Result<ExprKind> {
    let mut expander = KernelExpander {
        map: kernel,
        changed: false,
        builtin_modules,
        environment: None,
        depth: 0,
        allowed_macros: None,
        define_context: None,
        in_scope_values: ScopeSet::default(),
        globals,
    };
    expander.visit(&mut expr)?;

    Ok(expr)
}

pub struct KernelExpander<'a> {
    map: Option<&'a mut Kernel>,
    pub(crate) changed: bool,
    builtin_modules: ModuleContainer,
    environment: Option<&'a str>,
    depth: usize,
    allowed_macros: Option<&'a FxHashSet<InternedString>>,
    define_context: Option<ExprKind>,
    in_scope_values: ScopeSet<InternedString, FxBuildHasher>,
    globals: GlobalMap<'a>,
}

impl<'a> KernelExpander<'a> {
    fn visit_body(&mut self, exprs: &mut [ExprKind]) -> Result<()> {
        if self.map.is_none() {
            // Macros are already expanded, so this lowers every native head before any body and
            // records every definition.
            let (changed, _) =
                lower_native_definitions(exprs, self.globals, &mut self.in_scope_values, &|_| {
                    false
                })?;
            self.changed |= changed;
        } else {
            collect_defines(exprs, &mut |name| {
                self.in_scope_values.define(name);
            });
        }
        exprs.iter_mut().try_for_each(|expr| self.visit(expr))
    }

    pub fn new(
        map: Option<&'a mut Kernel>,
        builtin_modules: ModuleContainer,
        globals: GlobalMap<'a>,
    ) -> Self {
        Self {
            map,
            changed: false,
            builtin_modules,
            environment: None,
            depth: 0,
            allowed_macros: None,
            define_context: None,
            in_scope_values: ScopeSet::default(),
            globals,
        }
    }

    pub fn expand(&mut self, mut expr: ExprKind) -> Result<ExprKind> {
        self.visit(&mut expr)?;

        Ok(expr)
    }
}

fn expr_usize(value: usize) -> ExprKind {
    ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Number(
        NumberLiteral::Real(steel_parser::tokens::RealLiteral::Int(
            steel_parser::tokens::IntLiteral::Small(value as _),
        ))
        .into(),
    ))))
}

// Requirements:
// - Don't actually implement using a hashmap. Most likely
//   not necessary, and we don't need to introduce _another_
//   allocation into a kwargs dictionary.
//
// - We can just provide this as a function where the default
//   value is provided to the plist-get function
//   if the value is not there.
//
// As a result, expansion with default arguments should look like this:
//
// (define (test-kwargs #:foo [foo 10] #:bar [bar 20])
//  (+ foo bar))
//
// (define test-kwargs (lambda args
//     (let [(foo (plist-try-get args 10))
//           (bar (plist-try-get args 20))]
//        (+ foo bar)))
//
// This gives us the ability to fetch args quickly - just one linear scan,
// no additional allocation beyond the rest args that are already getting allocated.
//
// Handling args with non defaults just means we'll just plist-get instead of plist-try-get
// with a default value. That more or less means we'll only do a handful of scans.
fn expand_keyword_and_default_arguments(
    lambda_function: &mut super::ast::LambdaFunction,
    define_name: &Option<ExprKind>,
) -> Result<()> {
    let is_rest = lambda_function.rest;

    // First, lets find the pairs of keyword args. These could be default or not.
    // The order of keyword args doesn't matter, and they can be interwoven with
    // non key word arguments.

    // kwargs - These are things that are of the format:
    // #:foo [foo 10] or #:foo foo.
    let mut keyword_map: SmallVec<[(&ExprKind, &ExprKind); 6]> = SmallVec::new();

    let mut non_keyword_or_default_args: SmallVec<[ExprKind; 6]> = lambda_function
        .args
        .iter()
        .take_while(|x| {
            !matches!(
                x,
                ExprKind::Atom(Atom {
                    syn: SyntaxObject {
                        ty: TokenType::Keyword(_),
                        ..
                    }
                }) | ExprKind::List(_)
            )
        })
        .cloned()
        .collect();

    enum MaybeDefault<'a> {
        Rest(&'a ExprKind),
        Positional(&'a ExprKind),
        DefaultArg(&'a ExprKind, &'a ExprKind),
    }

    // Fetch positional args this way as well
    let mut positional_args: Vec<MaybeDefault> = Vec::new();
    let mut iter = lambda_function.args.iter().peekable();
    let mut seen_default_or_kwarg = false;
    let mut seen_default = false;

    let mut required_positional_arg_count = 0;
    let mut optional_positional_arg_count = 0;

    let mut required_keyword_arg_count = 0;
    let mut optional_keyword_arg_count = 0;

    while let Some(next) = iter.next() {
        let is_keyword = matches!(
            next,
            ExprKind::Atom(Atom {
                syn: SyntaxObject {
                    ty: TokenType::Keyword(_),
                    ..
                }
            })
        );

        let is_default_arg = matches!(next, ExprKind::List(_));
        seen_default_or_kwarg = seen_default_or_kwarg || is_default_arg;

        if is_keyword {
            let value = iter.next();
            match value {
                Some(v) => {
                    if matches!(v, ExprKind::List(_)) {
                        optional_keyword_arg_count += 1;
                    } else {
                        required_keyword_arg_count += 1;
                    }

                    keyword_map.push((next, v));
                }
                None => {
                    stop!(BadSyntax => format!("keyword arg missing variable name: {}", next); lambda_function.location.span)
                }
            }

            seen_default_or_kwarg = true;
        } else if seen_default_or_kwarg {
            match next {
                ExprKind::Atom(a) => {
                    if is_rest && iter.peek().is_none() {
                        positional_args.push(MaybeDefault::Rest(next))
                    } else {
                        if seen_default {
                            stop!(BadSyntax => "positional arg without default found after default argument"; a.syn.span)
                        }

                        required_positional_arg_count += 1;
                        positional_args.push(MaybeDefault::Positional(next))
                    }
                }
                ExprKind::List(l) => {
                    if l.len() != 2 {
                        stop!(BadSyntax => "malformed default argument"; lambda_function.location.span)
                    }

                    seen_default = true;

                    optional_positional_arg_count += 1;
                    positional_args.push(MaybeDefault::DefaultArg(
                        l.first().unwrap(),
                        l.get(1).unwrap(),
                    ));
                }
                _ => {
                    stop!(BadSyntax => "Internal compiler error")
                }
            }
        }
    }

    // Bail out if theres no keyword args or default arguments to expand
    if keyword_map.is_empty()
        && positional_args
            .iter()
            .all(|x| matches!(x, MaybeDefault::Positional(_)))
    {
        return Ok(());
    }

    let positional_arg_iter = positional_args
        .into_iter()
        .enumerate()
        .map(|(index, x)| match x {
            MaybeDefault::Rest(p) => {
                let mut p = p.clone();
                if let Some(var) = p.atom_syntax_object_mut() {
                    var.introduced_via_macro = true;
                }

                let expression = expr_list![
                    // TODO: this should actually be the call site span? How do we anchor against
                    // the calling function? Tail calls seem to mess that up - how do we reserve that
                    // information?
                    ExprKind::ident("#%prim.plist-get-positional-arg-list",),
                    ExprKind::ident(REST_ARG),
                    expr_usize(index),
                ];

                Ok((p.clone(), expression))
            }

            MaybeDefault::Positional(p) => {
                let mut p = p.clone();
                if let Some(var) = p.atom_syntax_object_mut() {
                    var.introduced_via_macro = true;
                }

                let expression = expr_list![
                    // TODO: this should actually be the call site span? How do we anchor against
                    // the calling function? Tail calls seem to mess that up - how do we reserve that
                    // information?
                    ExprKind::ident("#%prim.plist-get-positional-arg",),
                    ExprKind::ident(REST_ARG),
                    expr_usize(index),
                ];

                Ok((p.clone(), expression))
            }
            MaybeDefault::DefaultArg(p, default_value) => {
                let mut p = p.clone();
                if let Some(var) = p.atom_syntax_object_mut() {
                    var.introduced_via_macro = true;
                }

                let expression = expr_list![
                    // TODO: this should actually be the call site span? How do we anchor against
                    // the calling function? Tail calls seem to mess that up - how do we reserve that
                    // information?
                    ExprKind::ident("#%prim.plist-try-get-positional-arg",),
                    ExprKind::ident(REST_ARG),
                    ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Number(
                        NumberLiteral::Real(steel_parser::tokens::RealLiteral::Int(
                            steel_parser::tokens::IntLiteral::Small(index as _)
                        ))
                        .into()
                    )))),
                    default_value.clone()
                ];

                Ok((p.clone(), expression))
            }
        });

    let bindings = keyword_map
        .into_iter()
        .map(|x| {
            let keyword = x.0;
            let original_var_name = x.1;
            let mut required_kwarg = false;

            // This is a bit wasteful... come back to this
            let (mut var_name, expr) = if let ExprKind::List(l) = original_var_name {
                if l.len() != 2 {
                    stop!(BadSyntax => "Missing default argument for keyword"; 
                        lambda_function.location.span)
                }

                (l[0].clone(), l[1].clone())
            } else {
                required_kwarg = true;

                (original_var_name.clone(), original_var_name.clone())
            };

            if let Some(var) = var_name.atom_syntax_object_mut() {
                var.introduced_via_macro = true;
            }

            let mut expression = if required_kwarg {
                expr_list![
                    // TODO: this should actually be the call site span? How do we anchor against
                    // the calling function? Tail calls seem to mess that up - how do we reserve that
                    // information?
                    ExprKind::ident("#%prim.plist-get-kwarg",),
                    ExprKind::ident(REST_ARG),
                    ExprKind::Quote(Box::new(Quote::new(
                        keyword.clone(),
                        lambda_function.location.clone(),
                    ))),
                    ExprKind::Quote(Box::new(Quote::new(
                        define_name
                            .clone()
                            .unwrap_or_else(|| ExprKind::ident("anonymous function")),
                        lambda_function.location.clone()
                    )))
                ]
            } else {
                expr_list![
                    ExprKind::ident("#%prim.plist-try-get"),
                    ExprKind::ident(REST_ARG),
                    ExprKind::Quote(Box::new(Quote::new(
                        keyword.clone(),
                        lambda_function.location.clone(),
                    ))),
                    expr
                ]
            };

            if let ExprKind::List(l) = &mut expression {
                l.location = lambda_function.location.span;
            } else {
                unreachable!()
            }

            Ok((var_name, expression))
        })
        .chain(positional_arg_iter)
        .collect::<Result<Vec<_>>>()?;

    // if let Some(rest_arg) =

    // TODO: Pick up all keyword args before the start
    non_keyword_or_default_args.push(ExprKind::ident(REST_ARG));

    let mut inner_application = thin_vec![ExprKind::LambdaFunction(Box::new(LambdaFunction::new(
        bindings.iter().map(|x| x.0.clone()).collect(),
        lambda_function.body.clone(),
        SyntaxObject::default(TokenType::Lambda),
    )))];

    inner_application.extend(bindings.iter().map(|x| x.1.clone()));

    // TODO: This check has to be a little bit better.
    // For this to behave, we have to check the arity of the positional arguments,
    // as well as the non positional args. To do so, we should
    // just count the length of kwargs provided, as well as the length
    // of the positional args.
    //
    // Required positional and keyword args will count for 1 and 2 spaces
    // at the callsite, respectively.
    let arity_check_condition = ExprKind::If(Box::new(ast::If::new(
        ExprKind::List(List::new(thin_vec![
            ExprKind::ident("#%prim.plist-validate-args"),
            ExprKind::ident(REST_ARG),
            expr_usize(required_keyword_arg_count),
            expr_usize(required_positional_arg_count),
            expr_usize(optional_keyword_arg_count),
            expr_usize(optional_positional_arg_count),
            ExprKind::bool_lit(is_rest),
        ])),
        ExprKind::List(List::new(inner_application)),
        expr_list![
            ExprKind::ident("#%prim.error-with-span"),
            expr_list![ExprKind::ident("#%prim.current-function-span")],
            ExprKind::string_lit(format!(
                "Optional args - arity mismatch: {}",
                define_name
                    .clone()
                    .unwrap_or_else(|| ExprKind::ident("anonymous function")),
            ))
        ],
        SyntaxObject::default(TokenType::If),
    )));

    *lambda_function = LambdaFunction::new_with_rest_arg(
        non_keyword_or_default_args.into_iter().collect(),
        arity_check_condition,
        SyntaxObject::default(TokenType::Lambda),
    );

    Ok(())
}

// Lower the native binding forms heading top-level statements, up to the first statement whose
// head `is_macro`, where a head is shadowed by the bindings in `globals` or before it.
// Return how many statements were prepared; the caller records their definitions.
pub(crate) fn prepare_native_globals(
    exprs: &mut [ExprKind],
    globals: GlobalMap,
    is_macro: &dyn Fn(&InternedString) -> bool,
) -> Result<usize> {
    let (_, count) = lower_native_definitions(exprs, globals, &mut ScopeSet::default(), is_macro)?;
    Ok(count)
}

// Lower each statement headed by a native `define-values` or `struct` in order, recording every
// statement's definitions in `scope` as it goes, so a head sees only the bindings before it.
// Bodies are expanded afterwards, once every definition is known. Stop at a statement whose head
// `is_macro`, since its expansion can bind names that change later heads.
// Return the changed flag and the number of statements prepared.
fn lower_native_definitions(
    exprs: &mut [ExprKind],
    globals: GlobalMap,
    scope: &mut ScopeSet<InternedString, FxBuildHasher>,
    is_macro: &dyn Fn(&InternedString) -> bool,
) -> Result<(bool, usize)> {
    let mut changed = false;
    for (index, expr) in exprs.iter_mut().enumerate() {
        match expr {
            ExprKind::Begin(begin) => {
                let (nested_changed, prepared) =
                    lower_native_definitions(&mut begin.exprs, globals, scope, is_macro)?;
                changed |= nested_changed;
                if prepared < begin.exprs.len() {
                    return Ok((changed, index));
                }
                continue;
            }
            ExprKind::List(list) if list.first().is_some_and(is_begin_head) => {
                let (nested_changed, prepared) =
                    lower_native_definitions(&mut list.args[1..], globals, scope, is_macro)?;
                changed |= nested_changed;
                if prepared < list.args.len() - 1 {
                    return Ok((changed, index));
                }
                continue;
            }
            ExprKind::List(list) => {
                // Macros take precedence over native forms of the same name.
                if list.first_ident().is_some_and(is_macro) {
                    return Ok((changed, index));
                }
                // Leave the producer and field accessors for normal expansion.
                if let Some(lowered) =
                    lower_native_form(list, globals, |name| scope.contains(name))?
                {
                    *expr = lowered;
                    changed = true;
                }
            }
            _ => {}
        }
        collect_defines(std::slice::from_ref(expr), &mut |name| {
            scope.define(name);
        });
    }
    Ok((changed, exprs.len()))
}

// Lower `list` when it is headed by a native `define-values` or `struct` that `is_bound` does not
// shadow.
fn lower_native_form(
    list: &List,
    globals: GlobalMap,
    is_bound: impl Fn(&InternedString) -> bool,
) -> Result<Option<ExprKind>> {
    let is_bound = |name| {
        if list
            .first()
            .and_then(ExprKind::atom_syntax_object)
            .is_some_and(|syntax| syntax.global_reference)
        {
            // Global template heads resolve at their definition site, outside module bindings.
            match globals {
                GlobalMap::Map(_) | GlobalMap::Layered(_, _) => globals.actually_contains(name),
                GlobalMap::Set(_) => false,
                GlobalMap::Scoped(globals, _) => globals.actually_contains(name),
            }
        } else {
            is_bound(name) || globals.actually_contains(name)
        }
    };
    // Check the head's name before its bindings, since nearly every list is neither form.
    match list.first_ident() {
        Some(name) if name.resolve() == "define-values" && !is_bound(name) => {
            expand_define_values(list).map(Some)
        }
        Some(name) if name.resolve() == "struct" && !is_bound(name) => {
            expand_immutable_struct(list).map(Some)
        }
        _ => Ok(None),
    }
}

// Record the bindings of the native definitions heading top-level statements as if each were
// lowered in order, so a body can see a native definition that a later macro call keeps from
// being prepared yet. Heads see the names `is_head` accepts and the statements before them. Macro
// calls are skipped, and malformed forms are left to report their errors when they are prepared.
pub(crate) fn predeclare_native_definitions(
    exprs: &[ExprKind],
    is_head: &dyn Fn(&InternedString) -> bool,
    globals: GlobalMap,
    is_macro: &dyn Fn(&InternedString) -> bool,
    builtin_modules: Option<&ModuleContainer>,
    define: &mut impl FnMut(InternedString),
) {
    fn walk(
        exprs: &[ExprKind],
        is_head: &dyn Fn(&InternedString) -> bool,
        globals: GlobalMap,
        scope: &mut ScopeSet<InternedString, FxBuildHasher>,
        is_macro: &dyn Fn(&InternedString) -> bool,
        builtin_modules: Option<&ModuleContainer>,
        define: &mut impl FnMut(InternedString),
    ) {
        for expr in exprs {
            let lowered = match expr {
                ExprKind::Begin(begin) => {
                    walk(
                        &begin.exprs,
                        is_head,
                        globals,
                        scope,
                        is_macro,
                        builtin_modules,
                        define,
                    );
                    continue;
                }
                ExprKind::List(list) if list.first().is_some_and(is_begin_head) => {
                    walk(
                        &list.args[1..],
                        is_head,
                        globals,
                        scope,
                        is_macro,
                        builtin_modules,
                        define,
                    );
                    continue;
                }
                ExprKind::List(list) if list.first_ident().is_some_and(is_macro) => continue,
                ExprKind::List(list) if list.first_ident() == Some(&*REQUIRE_BUILTIN) => {
                    builtin_modules
                        .and_then(|modules| expand_require_builtin(&list.args[1..], modules).ok())
                }
                ExprKind::List(list) => {
                    lower_native_form(list, globals, |name| is_head(name) || scope.contains(name))
                        .ok()
                        .flatten()
                }
                _ => None,
            };
            collect_defines(
                std::slice::from_ref(lowered.as_ref().unwrap_or(expr)),
                &mut |name| {
                    scope.define(name);
                    define(name);
                },
            );
        }
    }
    walk(
        exprs,
        is_head,
        globals,
        &mut ScopeSet::default(),
        is_macro,
        builtin_modules,
        define,
    );
}

fn expand_define_values(list: &List) -> Result<ExprKind> {
    let span = get_span(&ExprKind::List(list.clone()));
    if list.improper || list.len() != 3 {
        stop!(BadSyntax => "define-values expects (define-values (name ...) producer)"; span)
    }
    let ExprKind::List(bindings) = &list.args[1] else {
        stop!(BadSyntax => "define-values expects a list of identifiers"; list.args[1].span())
    };
    if bindings.improper {
        stop!(BadSyntax => "define-values expects a proper list of identifiers"; list.args[1].span())
    }
    let mut seen = HashSet::new();
    for binding in &bindings.args {
        let Some(name) = binding.atom_identifier() else {
            stop!(BadSyntax => "define-values binding must be an identifier"; binding.span())
        };
        if !seen.insert(*name) {
            stop!(BadSyntax => "duplicate define-values binding"; binding.span())
        }
    }
    // Allocate an expansion identity: two invocations may have identical source spans.
    let location = SyntaxObject::new(TokenType::Define, span);
    let temporary = ExprKind::ident_with_span(
        &format!("##define-values-{}", u32::from(location.syntax_object_id)),
        span,
    );
    let primitive = |name: &str| {
        let mut identifier = ExprKind::ident_with_span(name, span);
        if let Some(syntax) = identifier.atom_syntax_object_mut() {
            syntax.unresolved = true;
            syntax.introduced_via_macro = true;
        }
        identifier
    };
    let mut definitions = vec![ExprKind::Define(Box::new(Define::new(
        temporary.clone(),
        expr_list![
            primitive("#%values-destructure"),
            list.args[2].clone(),
            expr_usize(bindings.len())
        ],
        location.clone(),
    )))];
    for (index, binding) in bindings.args.iter().enumerate() {
        definitions.push(ExprKind::Define(Box::new(Define::new(
            binding.clone(),
            expr_list![
                primitive("#%values-ref"),
                temporary.clone(),
                expr_usize(index)
            ],
            location.clone(),
        ))));
    }
    definitions.push(ExprKind::Set(Box::new(ast::Set::new(
        temporary,
        ExprKind::Atom(Atom::new(SyntaxObject::new(
            TokenType::BooleanLiteral(false),
            span,
        ))),
        SyntaxObject::new(TokenType::Set, span),
    ))));
    Ok(ExprKind::Begin(Box::new(Begin::new(
        definitions,
        SyntaxObject::new(TokenType::Begin, span),
    ))))
}

fn expand_immutable_struct(list: &List) -> Result<ExprKind> {
    let span = get_span(&ExprKind::List(list.clone()));
    if list.len() != 3 {
        stop!(BadSyntax => "no-kernel struct expects (struct name (field ...)); options are unsupported"; span)
    }
    let Some(name) = list.args[1].atom_identifier() else {
        stop!(BadSyntax => "struct expects an identifier for its name"; list.args[1].span())
    };
    let ExprKind::List(fields) = &list.args[2] else {
        stop!(BadSyntax => "struct expects a list of field identifiers"; list.args[2].span())
    };
    let mut seen = HashSet::new();
    for field in &fields.args {
        let Some(field_name) = field.atom_identifier() else {
            stop!(BadSyntax => "struct field must be an identifier"; field.span())
        };
        if !seen.insert(*field_name) {
            stop!(BadSyntax => "duplicate struct field"; field.span())
        }
    }
    if fields.len() > 65535 {
        stop!(BadSyntax => "struct exceeds 65535 fields"; span)
    }
    let location = SyntaxObject::new(TokenType::Define, span);
    let temporary = ExprKind::ident_with_span(
        &format!(
            "##immutable-struct-{}",
            u32::from(location.syntax_object_id)
        ),
        span,
    );
    let primitive = |name: &str| {
        let mut identifier = ExprKind::ident_with_span(name, span);
        if let Some(syntax) = identifier.atom_syntax_object_mut() {
            syntax.unresolved = true;
            syntax.introduced_via_macro = true;
        }
        identifier
    };
    let mut definitions = vec![ExprKind::Define(Box::new(Define::new(
        temporary.clone(),
        expr_list![
            primitive("#%immutable-struct-type"),
            ExprKind::Quote(Box::new(Quote::new(
                list.args[1].clone(),
                SyntaxObject::new(TokenType::Quote, span)
            ))),
            expr_usize(fields.len())
        ],
        location.clone(),
    )))];
    let names = std::iter::once(list.args[1].clone())
        .chain(std::iter::once(ExprKind::ident_with_span(
            &format!("{}?", name.resolve()),
            span,
        )))
        .chain(fields.args.iter().map(|field| {
            ExprKind::ident_with_span(
                &format!(
                    "{}-{}",
                    name.resolve(),
                    field.atom_identifier().unwrap().resolve()
                ),
                field.span(),
            )
        }));
    for (index, binding) in names.enumerate() {
        definitions.push(ExprKind::Define(Box::new(Define::new(
            binding,
            expr_list![temporary.clone(), expr_usize(index)],
            location.clone(),
        ))));
    }
    Ok(ExprKind::Begin(Box::new(Begin::new(
        definitions,
        SyntaxObject::new(TokenType::Begin, span),
    ))))
}

// VisitorMutRef
impl<'a> VisitorMutRef for KernelExpander<'a> {
    type Output = Result<()>;

    fn visit_if(&mut self, f: &mut super::ast::If) -> Self::Output {
        self.visit(&mut f.test_expr)?;
        self.visit(&mut f.then_expr)?;
        self.visit(&mut f.else_expr)
    }

    fn visit_define(&mut self, define: &mut super::ast::Define) -> Self::Output {
        // Early lowering bypasses the list-head normalization for this reserved name.
        if let Some(syntax) = define.name.atom_syntax_object_mut() {
            if syntax.ty == TokenType::DefineSyntax {
                syntax.ty = TokenType::Identifier(*DEFINE_SYNTAX);
            }
        }
        if let Some(ident) = define.name.atom_identifier() {
            self.in_scope_values.define(*ident);
        }
        self.define_context = Some(define.name.clone());
        self.visit(&mut define.body)?;
        self.define_context = None;

        Ok(())
    }

    // TODO: Kernel expander should have the liberty to parse everything
    // As a normal expression in order to match behavior
    fn visit_lambda_function(
        &mut self,
        lambda_function: &mut super::ast::LambdaFunction,
    ) -> Self::Output {
        {
            self.in_scope_values.push_layer();

            for value in &lambda_function.args {
                if let Some(ident) = value.atom_identifier() {
                    self.in_scope_values.define(*ident);
                }
            }

            for value in &mut lambda_function.args {
                self.visit(value)?;
            }

            // Without a kernel, `visit_body` records the body's definitions in order.
            if self.map.is_some() {
                collect_defines(std::slice::from_ref(&lambda_function.body), &mut |name| {
                    self.in_scope_values.define(name);
                });
            }
            self.visit(&mut lambda_function.body)?;

            self.in_scope_values.pop_layer();
        }

        // TODO: Unfortunately this wipes out the span
        // There needs to be

        // self.visit(&mut lambda_function.body)?;

        // Expand keyword arguments if we can
        // TODO: If this isn't a lambda function, we're gonna have problems
        // if its a list, we should run the same thing, but on a list
        // that starts with lambda, and coerce it to be expanded that way
        // expand_keyword_arguments(lambda_function)?;

        expand_keyword_and_default_arguments(lambda_function, &self.define_context)?;

        Ok(())
    }

    fn visit_begin(&mut self, begin: &mut super::ast::Begin) -> Self::Output {
        self.visit_body(&mut begin.exprs)
    }

    fn visit_return(&mut self, r: &mut super::ast::Return) -> Self::Output {
        self.visit(&mut r.expr)
    }

    fn visit_quote(&mut self, _quote: &mut super::ast::Quote) -> Self::Output {
        // TODO: We probably should not visit this here
        // self.visit(&mut quote.expr)
        Ok(())
    }

    fn visit_macro(&mut self, m: &mut super::ast::Macro) -> Self::Output {
        stop!(BadSyntax => format!("unexpected macro definition in kernel expander: {}", m); m.location.span)
    }

    fn visit_atom(&mut self, _a: &mut Atom) -> Self::Output {
        Ok(())
    }

    fn visit_list(&mut self, _l: &mut super::ast::List) -> Self::Output {
        Ok(())
    }

    fn visit_syntax_rules(&mut self, l: &mut super::ast::SyntaxRules) -> Self::Output {
        stop!(Generic => "unexpected syntax-rules definition"; l.location.span)
    }

    fn visit_set(&mut self, s: &mut super::ast::Set) -> Self::Output {
        self.visit(&mut s.variable)?;
        self.visit(&mut s.expr)?;

        Ok(())
    }

    fn visit_require(&mut self, _s: &mut super::ast::Require) -> Self::Output {
        Ok(())
    }

    fn visit_let(&mut self, l: &mut super::ast::Let) -> Self::Output {
        self.in_scope_values.push_layer();

        for (binding, _) in l.bindings.iter_mut() {
            if let Some(ident) = binding.atom_identifier() {
                self.in_scope_values.define(*ident);
            }
        }

        for (binding, expr) in l.bindings.iter_mut() {
            self.visit(binding)?;
            self.visit(expr)?;
        }

        // Without a kernel, `visit_body` records the body's definitions in order.
        if self.map.is_some() {
            collect_defines(std::slice::from_ref(&l.body_expr), &mut |name| {
                self.in_scope_values.define(name);
            });
        }
        self.visit(&mut l.body_expr)?;

        self.in_scope_values.pop_layer();

        Ok(())
    }

    fn visit(&mut self, expr: &mut ExprKind) -> Self::Output {
        if self.depth > 96 {
            stop!(BadSyntax => "Current expansion depth of defmacro style macros exceeded: depth capped at 96"; get_span(expr));
        }

        let res = match expr {
            ExprKind::If(f) => self.visit_if(f),
            ExprKind::Define(d) => self.visit_define(d),
            ExprKind::LambdaFunction(l) => self.visit_lambda_function(l),
            ExprKind::Begin(b) => self.visit_begin(b),
            ExprKind::Return(r) => self.visit_return(r),
            ExprKind::Let(l) => self.visit_let(l),
            ExprKind::Quote(q) => self.visit_quote(q),
            ExprKind::Macro(m) => self.visit_macro(m),
            ExprKind::Atom(a) => self.visit_atom(a),
            ExprKind::List(l) => {
                // Quoted data is not code, so definitions in quoted templates stay unlowered.
                if l.first().is_some_and(|head| {
                    head.atom_syntax_object()
                        .is_some_and(|syntax| match syntax.ty {
                            TokenType::Quote => true,
                            TokenType::Identifier(name) => name == *QUOTE,
                            _ => false,
                        })
                }) {
                    return Ok(());
                }
                if l.first().is_some_and(is_begin_head) {
                    return self.visit_body(&mut l.args[1..]);
                }
                if l.first().is_some_and(|head| {
                    head.atom_syntax_object()
                        .is_some_and(|syntax| matches!(syntax.ty, TokenType::Define))
                }) {
                    let list = core::mem::replace(l, List::new(ThinVec::new()));
                    *expr = ExprKind::try_from(list.args_proper(TokenType::Define)?)?;
                    return self.visit(expr);
                }
                // Macro signatures are binding data, not executable applications.
                if l.first_ident()
                    .is_some_and(|name| name.resolve() == "#%define-syntax")
                {
                    for body in l.args.iter_mut().skip(2) {
                        self.visit(body)?;
                    }
                    return Ok(());
                }
                if self.map.is_none() {
                    if let Some(lowered) = lower_native_form(l, self.globals, |name| {
                        self.in_scope_values.contains(name)
                    })? {
                        *expr = lowered;
                        self.changed = true;
                        return self.visit(expr);
                    }
                }

                {
                    match l.first() {
                        Some(head) if is_let_head(head) => {
                            return visit_let_form(
                                self,
                                |v| &mut v.in_scope_values,
                                l,
                                Self::visit_body,
                            );
                        }
                        Some(ExprKind::Atom(ident))
                            if ident.syn.ty == TokenType::Lambda
                                || matches!(ident.syn.ty, TokenType::Identifier(name)
                                    if name == *LAMBDA_SYMBOL || name == *LAMBDA) =>
                        {
                            let ident = ident.clone();
                            // The list is replaced by the parsed lambda, so move it instead of
                            // cloning the whole body.
                            let list = core::mem::replace(l, List::new(ThinVec::new()));
                            if let ExprKind::LambdaFunction(mut lambda) =
                                parse_lambda(ident, list.args_proper(TokenType::Lambda)?)?
                            {
                                self.visit_lambda_function(&mut lambda)?;

                                *expr = ExprKind::LambdaFunction(lambda);

                                return Ok(());

                                // return self.visit_lambda_function(&mut lambda);

                                // return self.visit_lambda_function(lambda);
                            } else {
                                unreachable!()
                            }
                        }

                        _ => {}
                    }

                    if l.first()
                        .map(|x| {
                            if let ExprKind::Atom(Atom {
                                syn:
                                    SyntaxObject {
                                        ty: TokenType::DefineSyntax,
                                        ..
                                    },
                            }) = x
                            {
                                true
                            } else {
                                false
                            }
                        })
                        .unwrap_or_default()
                    {
                        if let Some(arg) = l.args.get_mut(2) {
                            self.visit(arg)?;
                            return Ok(());
                        }
                    }

                    if l.first()
                        .map(|x| {
                            if let ExprKind::Atom(Atom {
                                syn:
                                    SyntaxObject {
                                        ty: TokenType::SyntaxRules,
                                        ..
                                    },
                            }) = x
                            {
                                true
                            } else {
                                false
                            }
                        })
                        .unwrap_or_default()
                    {
                        if let Some(args) = l.args.get_mut(2..) {
                            for arg in args {
                                self.visit(arg)?;
                            }
                            return Ok(());
                        }
                    }

                    if let Some(s) = l.first().and_then(|x| {
                        if let ExprKind::Atom(Atom {
                            syn:
                                SyntaxObject {
                                    ty: TokenType::Identifier(s),
                                    ..
                                },
                        }) = x
                        {
                            Some(*s)
                        } else {
                            None
                        }
                    }) {
                        if s == *SYNTAX_CASE {
                            if let Some(args) = l.args.get_mut(3..) {
                                for arg in args {
                                    if let ExprKind::List(l) = arg {
                                        if let Some(rest) = l.args.get_mut(1..) {
                                            for arg in rest {
                                                self.visit(arg)?;
                                            }
                                        }
                                    } else {
                                        self.visit(arg)?;
                                    }
                                }

                                return Ok(());
                            }
                        }

                        if let Some(map) = &mut self.map {
                            if map.contains_syntax_object_macro(
                                &s,
                                self.environment.as_ref().map(|x| x.as_ref()),
                            ) && self
                                .allowed_macros
                                .as_ref()
                                .map(|x| x.contains(&s))
                                .unwrap_or(true)
                            {
                                let mut expanded = map.expand_syntax_object(
                                    &s,
                                    ExprKind::List(core::mem::replace(
                                        l,
                                        List::new(ThinVec::new()),
                                    )),
                                    self.environment
                                        .as_ref()
                                        .map(|x| x.as_ref())
                                        .unwrap_or("default"),
                                    &self.in_scope_values,
                                    self.globals,
                                )?;
                                self.changed = true;

                                self.depth += 1;

                                self.visit(&mut expanded)?;

                                self.depth -= 1;

                                *expr = expanded;

                                return Ok(());

                                // return result;
                            }
                        }

                        if s == *REQUIRE_BUILTIN {
                            *expr = expand_require_builtin(&l.args[1..], &self.builtin_modules)?;
                            return Ok(());
                        }
                    }

                    for expr in l.args.iter_mut() {
                        self.visit(expr)?;
                    }

                    Ok(())
                }
            }
            ExprKind::SyntaxRules(s) => self.visit_syntax_rules(s),
            ExprKind::Set(s) => self.visit_set(s),
            ExprKind::Require(r) => self.visit_require(r),
            ExprKind::Vector(v) => self.visit_vector(v),
        };

        res
    }

    fn visit_vector(&mut self, _v: &mut super::ast::Vector) -> Self::Output {
        Ok(())
    }
}

fn expand_require_builtin(
    args: &[ExprKind],
    builtin_modules: &ModuleContainer,
) -> Result<ExprKind> {
    let (module, prefix) = match args {
        [module] => (module, None),
        [module, as_keyword, prefix]
            if as_keyword.atom_identifier() == Some(&*AS_KEYWORD)
                && prefix.atom_identifier().is_some() =>
        {
            (module, prefix.atom_identifier().map(|name| name.resolve()))
        }
        _ => {
            stop!(ArityMismatch => "require-builtin malformed - follows the pattern (require-builtin \"<module>\") or (require-builtin \"<module>\" as <prefix>)")
        }
    };
    match module {
        ExprKind::Atom(Atom {
            syn:
                SyntaxObject {
                    ty: TokenType::StringLiteral(name) | TokenType::Identifier(name),
                    span,
                    ..
                },
        }) => {
            if let Some(module) = builtin_modules.get(name.resolve()) {
                Ok(module.to_syntax(prefix))
            } else {
                stop!(BadSyntax => format!("require-builtin: module not found: {}", name); *span)
            }
        }
        _ => {
            stop!(ArityMismatch => "require-builtin malformed - follows the pattern (require-builtin \"<module>\") or (require-builtin \"<module>\" as <prefix>)")
        }
    }
}

fn _define_quoted_ast_node(ast_name: ExprKind, expanded_expr: &ExprKind) -> ExprKind {
    ExprKind::Define(Box::new(Define::new(
        ast_name,
        ExprKind::Quote(Box::new(Quote::new(
            expanded_expr.clone(),
            SyntaxObject::default(TokenType::Quote),
        ))),
        SyntaxObject::default(TokenType::Define),
    )))
}

#[cfg(test)]
mod expansion_tests {
    use steel_parser::span::Span;

    use super::*;

    use crate::parser::expander::MacroCase;
    use crate::parser::expander::MacroPattern;

    use crate::parser::ast::{Begin, If, List};
    use crate::parser::expander::PatternList;
    use crate::parser::tokens::TokenType;

    fn atom_identifier(s: &str) -> ExprKind {
        ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Identifier(
            s.into(),
        ))))
    }

    fn ellipses() -> ExprKind {
        ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Ellipses)))
    }

    #[test]
    fn native_forms_predeclare_lowered_and_unlowered_bindings() {
        for name in ["struct", "define-values"] {
            for source in [
                format!("(begin (define (call) ({name} 42)) (begin (define ({name} x) x)))"),
                format!("(lambda () (define (call) ({name} 42)) (begin (define {name} (lambda (x) x))) (call))"),
                format!("(let ((x 42)) (define (call) ({name} x)) (begin (define ({name} x) x)) (call))"),
            ] {
                for mut ast in [
                    steel_parser::parser::Parser::parse(&source).unwrap(),
                    steel_parser::parser::Parser::parse_without_lowering(&source).unwrap(),
                ] {
                    assert!(!expand_kernel_in_env_with_change(
                        &mut ast[0], None, ModuleContainer::default(), "top-level",
                        GlobalMap::Map(&FxHashMap::default()),
                    ).unwrap(), "{source}");
                }
            }
            let mut ast =
                steel_parser::parser::Parser::parse_without_lowering(&format!("({name} 42)"))
                    .unwrap();
            assert!(!expand_kernel_in_env_with_change(
                &mut ast[0],
                None,
                ModuleContainer::default(),
                "top-level",
                GlobalMap::Map(&[(name.into(), 0)].into_iter().collect()),
            )
            .unwrap());
        }
    }

    #[test]
    fn native_definitions_prepare_lowered_and_unlowered_scopes() {
        for name in ["struct", "define-values"] {
            let body = format!(
                "(define (call) ({name} 42))
                 (begin (begin (define-values ({name}) (lambda (x) x)))) (call)"
            );
            for source in [
                format!("(begin {body})"),
                format!("(lambda () {body})"),
                format!("(let () {body})"),
                format!("(let loop () {body})"),
                format!("(begin (begin (struct before (x))) {body})"),
                format!("(lambda () (begin (struct before (x))) {body})"),
                format!("(let () (begin (struct before (x))) {body})"),
                format!("(let loop () (begin (struct before (x))) {body})"),
            ] {
                for mut ast in [
                    steel_parser::parser::Parser::parse(&source).unwrap(),
                    steel_parser::parser::Parser::parse_without_lowering(&source).unwrap(),
                ] {
                    assert!(
                        expand_kernel_in_env_with_change(
                            &mut ast[0],
                            None,
                            ModuleContainer::default(),
                            "top-level",
                            GlobalMap::Map(&FxHashMap::default()),
                        )
                        .unwrap(),
                        "{source}"
                    );
                    assert!(
                        ast[0].to_string().contains(&format!("({name} 42)")),
                        "{source}"
                    );
                }
            }
        }
    }

    #[test]
    fn native_definitions_follow_expansion_in_lowered_and_unlowered_scopes() {
        for declaration in [
            "(struct define-values (x))",
            "(begin (begin (struct define-values (x))))",
        ] {
            let body = format!("{declaration} (define-values 42)");
            for source in [
                format!("(begin {body})"),
                format!("(lambda () {body})"),
                format!("(let () {body})"),
                format!("(let loop () {body})"),
            ] {
                for mut ast in [
                    steel_parser::parser::Parser::parse(&source).unwrap(),
                    steel_parser::parser::Parser::parse_without_lowering(&source).unwrap(),
                ] {
                    assert!(
                        expand_kernel_in_env_with_change(
                            &mut ast[0],
                            None,
                            ModuleContainer::default(),
                            "top-level",
                            GlobalMap::Map(&FxHashMap::default()),
                        )
                        .unwrap_or_else(|error| panic!("{source}: {error}")),
                        "{source}"
                    );
                    assert!(
                        ast[0].to_string().contains("(define-values 42)"),
                        "{source}"
                    );
                }
            }
        }
    }

    #[test]
    fn native_forms_skip_definition_signatures() {
        for source in [
            "(#%define-syntax (struct expr) (struct local (field)))",
            "(define (struct expr) (struct local (field)))",
            "(#%define-syntax (define-values expr) (struct local (field)))",
            "(define (define-values expr) (struct local (field)))",
        ] {
            let input = steel_parser::parser::Parser::parse_without_lowering(source)
                .unwrap()
                .remove(0);
            let expanded = expand_kernel(
                input.clone(),
                None,
                ModuleContainer::default(),
                GlobalMap::Set(&FxHashSet::default()),
            )
            .unwrap();
            let ExprKind::List(input) = input else {
                panic!("expected an unlowered input: {source}");
            };
            if source.starts_with("(define ") {
                let ExprKind::Define(define) = expanded else {
                    panic!("expected a lowered definition: {source}");
                };
                let ExprKind::List(signature) = &input.args[1] else {
                    panic!("expected a function signature: {source}");
                };
                assert_eq!(define.name, signature.args[0], "{source}");
                let ExprKind::LambdaFunction(lambda) = define.body else {
                    panic!("expected a lowered lambda: {source}");
                };
                assert_eq!(lambda.args[..], signature.args[1..], "{source}");
                if define.name.atom_identifier().unwrap().resolve() == "struct" {
                    assert!(matches!(lambda.body, ExprKind::List(_)), "{source}");
                } else {
                    assert!(matches!(lambda.body, ExprKind::Begin(_)), "{source}");
                }
            } else {
                let ExprKind::List(expanded) = expanded else {
                    panic!("expected an unlowered macro definition: {source}");
                };
                assert_eq!(input.args[..2], expanded.args[..2], "{source}");
                assert!(matches!(expanded.args[2], ExprKind::Begin(_)), "{source}");
            }
        }
    }

    #[test]
    fn test_basic_expansion() {
        // (define-syntax when
        //     (syntax-rules ()
        //       [(when a b ...)
        //        (if a (begin b ...) void)]))
        let m = SteelMacro::new(
            "when".into(),
            Vec::new(),
            vec![MacroCase::new(
                PatternList::new(vec![
                    MacroPattern::Syntax("when".into(), false),
                    MacroPattern::Single("a".into()),
                    MacroPattern::Many(MacroPattern::Single("b".into()).into()),
                ]),
                If::new(
                    atom_identifier("a"),
                    Begin::new(
                        vec![atom_identifier("b"), ellipses()],
                        SyntaxObject::default(TokenType::Begin),
                    )
                    .into(),
                    atom_identifier("void"),
                    SyntaxObject::default(TokenType::If),
                )
                .into(),
            )],
            Span::default(),
        );

        let mut map = FxHashMap::default();
        map.insert("when".into(), m);

        let mut input: ExprKind = List::new(thin_vec![
            atom_identifier("when"),
            atom_identifier("blagh"),
            atom_identifier("do-thing"),
        ])
        .into();

        let expected: ExprKind = If::new(
            atom_identifier("blagh"),
            Begin::new(
                vec![atom_identifier("do-thing")],
                SyntaxObject::default(TokenType::Begin),
            )
            .into(),
            atom_identifier("void"),
            SyntaxObject::default(TokenType::If),
        )
        .into();

        expand(&mut input, &map, GlobalMap::Set(&FxHashSet::default())).unwrap();

        assert_eq!(expected, input)
    }
}
