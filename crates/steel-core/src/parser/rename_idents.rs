use steel_parser::ast::{
    Atom, LAMBDA, LAMBDA_FN, PLAIN_LET, QUASIQUOTE, RAW_QUOTE, RAW_UNQUOTE, RAW_UNQUOTE_SPLICING,
    STRUCT_KEYWORD, UNQUOTE, UNQUOTE_COMMA, UNQUOTE_SPLICING,
};

use crate::compiler::passes::mangle::{collect_define_syntax, collect_defines};
use crate::compiler::passes::VisitorMutRefUnit;
use crate::compiler::program::{DATUM_SYNTAX, LAMBDA_SYMBOL};
use crate::parser::ast::ExprKind;
use crate::parser::expand_visitor::{predeclare_native_definitions, GlobalMap};
use crate::parser::expander::SteelMacro;
use crate::parser::parser::{ExpansionMark, SyntaxObject};
use crate::parser::tokens::TokenType;
use crate::parser::visitors::VisitorMutRef;
use crate::steel_vm::engine::ModuleContainer;

use quickscope::ScopeSet;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};

use super::interner::InternedString;

// Template identifiers bound by a nested macro, which are no longer free template references.
#[derive(Default)]
pub(crate) struct TemplateBindings(FxHashSet<(InternedString, ExpansionMark)>);

impl VisitorMutRefUnit for TemplateBindings {
    fn visit_atom(&mut self, atom: &mut Atom) {
        if let TokenType::Identifier(name) = atom.syn.ty {
            if self.0.contains(&(name, atom.syn.mark)) {
                atom.syn.global_reference = false;
                atom.syn.unresolved = false;
            }
        }
    }
}

impl TemplateBindings {
    // Record a parameter, either an identifier or the name of a `(name value)` binding.
    pub(crate) fn bind_parameter(&mut self, parameter: &ExprKind) {
        let name = match parameter {
            ExprKind::List(binding) => binding.args.first(),
            parameter => Some(parameter),
        };
        if let Some(syn) = name.and_then(ExprKind::atom_syntax_object) {
            if let TokenType::Identifier(name) = syn.ty {
                if syn.global_reference && syn.mark.is_template() {
                    self.0.insert((name, syn.mark));
                }
            }
        }
    }

    pub(crate) fn resolve(&mut self, expr: &mut ExprKind) {
        if !self.0.is_empty() {
            self.visit(expr);
        }
    }
}

pub(crate) fn resolve_template_bindings(exprs: &mut [ExprKind], expanded: std::ops::Range<usize>) {
    let mut bindings = TemplateBindings::default();
    collect_define_syntax(&exprs[expanded], &mut |name, syn| {
        if syn.mark.is_template() {
            bindings.0.insert((name, syn.mark));
        }
    });
    // Expansion and native lowering can bind previously free template references.
    for expr in exprs {
        bindings.resolve(expr);
    }
}

pub struct RenameIdentifiersVisitor<'a> {
    introduced_identifiers: ScopeSet<InternedString, FxBuildHasher>,
    pattern_variables: &'a [InternedString],
    syntax: &'a [InternedString],
    preserve_struct_fields: bool,
    preserved_struct_fields: bool,
    global_scope: Option<(
        &'a FxHashMap<InternedString, SteelMacro>,
        &'a ModuleContainer,
        GlobalMap<'a>,
    )>,
}

impl<'a> RenameIdentifiersVisitor<'a> {
    pub fn new(pattern_variables: &'a [InternedString], syntax: &'a [InternedString]) -> Self {
        RenameIdentifiersVisitor {
            introduced_identifiers: ScopeSet::default(),
            pattern_variables,
            syntax,
            preserve_struct_fields: false,
            preserved_struct_fields: false,
            global_scope: None,
        }
    }

    pub fn add(&mut self, ident: InternedString) {
        self.introduced_identifiers.define(ident);
    }

    pub fn is_gensym(&self, ident: &InternedString) -> bool {
        self.introduced_identifiers.contains(ident) || self.pattern_variables.contains(ident)
    }

    pub fn rename_identifiers(&mut self, expr: &mut ExprKind) {
        self.visit_body(std::slice::from_mut(expr));
    }

    pub(crate) fn rename_native_struct_template(&mut self, expr: &mut ExprKind) -> bool {
        self.preserve_struct_fields = true;
        self.rename_identifiers(expr);
        self.preserved_struct_fields
    }

    pub(crate) fn mark_global_references(
        expr: &mut ExprKind,
        macros: &'a FxHashMap<InternedString, SteelMacro>,
        builtin_modules: &'a ModuleContainer,
        globals: GlobalMap<'a>,
    ) {
        let mut visitor = Self::new(&[], &[]);
        // Template references resolve outside the calling module's bindings.
        let globals = match globals {
            GlobalMap::Scoped(globals, _) => *globals,
            globals => globals,
        };
        visitor.global_scope = Some((macros, builtin_modules, globals));
        visitor.visit_body(std::slice::from_mut(expr));
    }

    fn visit_body(&mut self, exprs: &mut [ExprKind]) {
        if let Some((macros, builtin_modules, globals)) = self.global_scope {
            // Heads see only the bindings before the body, so introduce its definitions after.
            let mut definitions = Vec::new();
            predeclare_native_definitions(
                exprs,
                &|name| self.introduced_identifiers.contains(name),
                globals,
                &|name| macros.contains_key(name),
                Some(builtin_modules),
                &mut |name| definitions.push(name),
            );
            for name in definitions {
                self.add(name);
            }
        } else {
            collect_defines(exprs, &mut |name| {
                if !self.pattern_variables.contains(&name) {
                    self.add(name);
                }
            });
        }
        for expr in exprs {
            self.visit(expr);
        }
    }

    fn bind(&mut self, expr: &mut ExprKind) {
        if let Some(syntax) = expr.atom_syntax_object_mut() {
            if let TokenType::Identifier(name) = syntax.ty {
                if !self.pattern_variables.contains(&name) {
                    self.add(name);
                }
                if self.global_scope.is_some() {
                    return;
                }
                *syntax = SyntaxObject::default(TokenType::Identifier(
                    ("##".to_string() + name.resolve()).into(),
                ));
                syntax.introduced_via_macro = true;
            }
        }
    }

    fn visit_parameters(&mut self, args: &mut [ExprKind]) {
        let positional_count = args
            .iter()
            .take_while(|arg| arg.atom_identifier().is_some())
            .count();
        for arg in &mut args[..positional_count] {
            self.bind(arg);
        }
        // Defaults see required positional parameters, but no optional or keyword bindings.
        for arg in &mut args[positional_count..] {
            if let ExprKind::List(binding) = arg {
                if let Some(default) = binding.args.get_mut(1) {
                    self.visit(default);
                }
            }
        }
        for arg in &mut args[positional_count..] {
            match arg {
                ExprKind::List(binding) => {
                    if let Some(name) = binding.args.first_mut() {
                        self.bind(name);
                    }
                }
                _ => self.bind(arg),
            }
        }
    }

    // Okay so this is annoying: we'll have to handle quoted data in the template.
    // A pattern variable is still replaced by its argument, but a name the template introduces stays
    // whatever it was before.
    fn visit_data(&mut self, expr: &mut ExprKind, depth: Option<usize>) {
        match expr {
            ExprKind::Atom(a) => {
                if let TokenType::Identifier(s) = a.syn.ty {
                    if self.pattern_variables.contains(&s) {
                        a.syn.ty = TokenType::Identifier(("##".to_string() + s.resolve()).into());
                    }
                }
            }
            ExprKind::List(l) => {
                let depth = match (depth, l.first_ident()) {
                    (Some(depth), Some(head)) if *head == *QUASIQUOTE => Some(depth + 1),
                    (Some(depth), Some(head)) if is_unquote(head) => Some(depth - 1),
                    (depth, _) => depth,
                };
                for expr in &mut l.args {
                    if depth == Some(0) {
                        self.visit(expr);
                    } else {
                        self.visit_data(expr, depth);
                    }
                }
            }
            ExprKind::Vector(v) => {
                for expr in &mut v.args {
                    self.visit_data(expr, depth);
                }
            }
            ExprKind::Quote(q) => self.visit_data(&mut q.expr, depth),
            _ => self.visit(expr),
        }
    }
}

fn is_unquote(head: &InternedString) -> bool {
    *head == *UNQUOTE
        || *head == *UNQUOTE_COMMA
        || *head == *RAW_UNQUOTE
        || *head == *UNQUOTE_SPLICING
        || *head == *RAW_UNQUOTE_SPLICING
}

impl<'a> VisitorMutRef for RenameIdentifiersVisitor<'a> {
    type Output = ();

    fn visit_if(&mut self, f: &mut super::ast::If) -> Self::Output {
        self.visit(&mut f.test_expr);
        self.visit(&mut f.then_expr);
        self.visit(&mut f.else_expr);
    }

    fn visit_define(&mut self, define: &mut super::ast::Define) -> Self::Output {
        self.bind(&mut define.name);
        self.visit(&mut define.body)
    }

    fn visit_lambda_function(
        &mut self,
        lambda_function: &mut super::ast::LambdaFunction,
    ) -> Self::Output {
        self.introduced_identifiers.push_layer();
        self.visit_parameters(&mut lambda_function.args);
        self.visit_body(std::slice::from_mut(&mut lambda_function.body));
        self.introduced_identifiers.pop_layer();
    }

    fn visit_begin(&mut self, begin: &mut super::ast::Begin) -> Self::Output {
        self.visit_body(&mut begin.exprs);
    }

    fn visit_return(&mut self, r: &mut super::ast::Return) -> Self::Output {
        self.visit(&mut r.expr)
    }

    fn visit_quote(&mut self, quote: &mut super::ast::Quote) -> Self::Output {
        self.visit_data(&mut quote.expr, None);
    }

    fn visit_macro(&mut self, _m: &mut super::ast::Macro) -> Self::Output {
        todo!()
    }

    fn visit_atom(&mut self, a: &mut super::ast::Atom) -> Self::Output {
        let token = a.syn.ty.clone();
        if let TokenType::Identifier(s) = token {
            if self.global_scope.is_some() {
                a.syn.unresolved = !self.introduced_identifiers.contains(&s);
                a.syn.global_reference |= a.syn.unresolved;
                return;
            }
            if self.syntax.contains(&s) || s == *DATUM_SYNTAX {
                return;
            }

            if self.is_gensym(&s) {
                a.syn.ty = TokenType::Identifier(("##".to_string() + s.resolve()).into());
            } else {
                a.syn.unresolved = true;
            }
        }
    }

    fn visit_list(&mut self, l: &mut super::ast::List) -> Self::Output {
        // TODO: So here, since this body isn't lowered all the way, we're not
        // actually _doing_ anything!
        match l.first() {
            Some(ExprKind::Atom(Atom {
                syn: SyntaxObject { ty, .. },
            })) if *ty == TokenType::Quote || *ty == TokenType::Identifier(*RAW_QUOTE) => {
                for expr in &mut l.args[1..] {
                    self.visit_data(expr, None);
                }
            }

            Some(ExprKind::Atom(Atom {
                syn: SyntaxObject { ty, .. },
            })) if *ty == TokenType::Identifier(*QUASIQUOTE) => {
                for expr in &mut l.args[1..] {
                    self.visit_data(expr, Some(1));
                }
            }

            Some(ExprKind::Atom(Atom {
                syn: SyntaxObject { ty, .. },
            })) if *ty == TokenType::Begin
                || *ty == TokenType::Identifier(*crate::compiler::program::BEGIN) =>
            {
                self.visit_body(&mut l.args[1..]);
            }

            // Some(ExprKind::Atom(Atom {
            //     syn: SyntaxObject { ty, .. },
            // })) if *ty == TokenType::Identifier(*DATUM_SYNTAX) => {
            //     for expr in &mut l.args {
            //         self.visit(expr);
            //     }
            // }
            Some(ExprKind::Atom(Atom {
                syn: SyntaxObject { ty, .. },
            })) if *ty == TokenType::Define => {
                let mut is_function = false;
                // TODO: Top level defines should be allowed to escape here
                match l.args.get_mut(1) {
                    // (define name expr)
                    Some(name @ ExprKind::Atom(_)) => self.bind(name),

                    // (define (name args ...) exprs ...)
                    Some(ExprKind::List(shorthand_define_function)) => {
                        if shorthand_define_function.first_ident() != Some(&*DATUM_SYNTAX) {
                            if let Some(name) = shorthand_define_function.args.first_mut() {
                                self.bind(name);
                            }
                            self.introduced_identifiers.push_layer();
                            is_function = true;
                            if let Some(args) = shorthand_define_function.args.get_mut(1..) {
                                self.visit_parameters(args);
                            }
                        }
                    }

                    _ => {}
                }

                if let Some(rest) = l.args.get_mut(2..) {
                    self.visit_body(rest);
                }
                if is_function {
                    self.introduced_identifiers.pop_layer();
                }
            }

            Some(ExprKind::Atom(Atom {
                syn: SyntaxObject { ty, .. },
            })) if *ty == TokenType::Lambda
                || *ty == TokenType::Identifier(*LAMBDA_SYMBOL)
                || *ty == TokenType::Identifier(*LAMBDA)
                || *ty == TokenType::Identifier(*LAMBDA_FN) =>
            {
                self.introduced_identifiers.push_layer();
                match l.args.get_mut(1) {
                    Some(ExprKind::List(arguments)) => self.visit_parameters(&mut arguments.args),
                    Some(arg) => self.bind(arg),
                    None => {}
                }

                if let Some(rest) = l.args.get_mut(2..) {
                    self.visit_body(rest);
                }
                self.introduced_identifiers.pop_layer();
            }

            Some(ExprKind::Atom(Atom {
                syn: SyntaxObject { ty, .. },
            })) if *ty == TokenType::Let || *ty == TokenType::Identifier(*PLAIN_LET) => {
                let named = l.args.get(1).and_then(ExprKind::atom_identifier).is_some();
                let bindings_index = if named { 2 } else { 1 };
                if let Some(ExprKind::List(bindings)) = l.args.get_mut(bindings_index) {
                    for pair in &mut bindings.args {
                        if let ExprKind::List(pair) = pair {
                            if let Some(value) = pair.args.get_mut(1) {
                                self.visit(value);
                            }
                        }
                    }
                }
                self.introduced_identifiers.push_layer();
                if named {
                    self.bind(&mut l.args[1]);
                }
                if let Some(ExprKind::List(bindings)) = l.args.get_mut(bindings_index) {
                    for pair in &mut bindings.args {
                        if let ExprKind::List(pair) = pair {
                            if let Some(name) = pair.args.first_mut() {
                                self.bind(name);
                            }
                        }
                    }
                }
                if let Some(remaining) = l.args.get_mut(bindings_index + 1..) {
                    self.visit_body(remaining);
                }
                self.introduced_identifiers.pop_layer();
            }

            _ => {
                let native_struct = self.preserve_struct_fields
                    && l.first_ident() == Some(&*STRUCT_KEYWORD)
                    && !self.is_gensym(&STRUCT_KEYWORD);
                for (index, expr) in l.args.iter_mut().enumerate() {
                    if native_struct && index == 1 {
                        let original_name = expr
                            .atom_identifier()
                            .copied()
                            .filter(|name| !self.pattern_variables.contains(name));
                        self.visit(expr);
                        if let Some(name) = original_name {
                            let syntax = expr.atom_syntax_object_mut().unwrap();
                            // Leave later call-site renaming intact when this template didn't rename the name.
                            if syntax.ty != TokenType::Identifier(name) {
                                syntax.original_name.get_or_insert(name);
                            }
                        }
                    } else if native_struct && index == 2 {
                        // Field names are data; only pattern variables need renaming.
                        self.preserved_struct_fields = true;
                        self.visit_data(expr, None);
                    } else {
                        self.visit(expr);
                    }
                }
            }
        }

        // for expr in &mut l.args {
        //     self.visit(expr);
        // }
    }

    fn visit_syntax_rules(&mut self, _l: &mut super::ast::SyntaxRules) -> Self::Output {
        todo!()
    }

    fn visit_set(&mut self, s: &mut super::ast::Set) -> Self::Output {
        self.visit(&mut s.variable);
        self.visit(&mut s.expr);
    }

    fn visit_require(&mut self, s: &mut super::ast::Require) -> Self::Output {
        for module in &mut s.modules {
            self.visit(module);
        }
    }

    fn visit_let(&mut self, l: &mut super::ast::Let) -> Self::Output {
        for (_, expr) in &mut l.bindings {
            self.visit(expr);
        }
        self.introduced_identifiers.push_layer();
        for (arg, _) in &mut l.bindings {
            self.bind(arg);
        }
        self.visit_body(std::slice::from_mut(&mut l.body_expr));
        self.introduced_identifiers.pop_layer();
    }

    fn visit_vector(&mut self, v: &mut super::ast::Vector) -> Self::Output {
        if v.bytes {
            return;
        }

        for arg in &mut v.args {
            self.visit(arg);
        }
    }
}

#[cfg(test)]
mod rename_visitor_tests {

    use steel_parser::tokens::IntLiteral;

    use super::TokenType::*;
    use super::*;
    use crate::parser::ast::{Atom, Define, If, LambdaFunction, List};

    use thin_vec::thin_vec;

    fn atom_identifier(s: &str) -> ExprKind {
        ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Identifier(
            s.into(),
        ))))
    }

    fn atom_int(n: isize) -> ExprKind {
        ExprKind::Atom(Atom::new(SyntaxObject::default(
            IntLiteral::Small(n).into(),
        )))
    }

    #[test]
    fn test_rename_identifiers() {
        let mut pre_condition = ExprKind::LambdaFunction(Box::new(LambdaFunction::new(
            thin_vec![ExprKind::Atom(Atom::new(SyntaxObject::default(
                Identifier("x".into()),
            )))],
            ExprKind::List(List::new(thin_vec![
                ExprKind::Atom(Atom::new(SyntaxObject::default(Identifier("+".into())))),
                ExprKind::Atom(Atom::new(SyntaxObject::default(Identifier("x".into())))),
                atom_int(10),
            ])),
            SyntaxObject::default(TokenType::Lambda),
        )));

        let post_condition = ExprKind::LambdaFunction(Box::new(LambdaFunction::new(
            thin_vec![ExprKind::Atom(Atom::new(SyntaxObject::default(
                Identifier("##x".into()),
            )))],
            ExprKind::List(List::new(thin_vec![
                ExprKind::Atom(Atom::new(SyntaxObject::default(Identifier("+".into())))),
                ExprKind::Atom(Atom::new(SyntaxObject::default(Identifier("##x".into())))),
                atom_int(10),
            ])),
            SyntaxObject::default(TokenType::Lambda),
        )));

        let mut visitor = RenameIdentifiersVisitor::new(&[], &[]);

        visitor.visit(&mut pre_condition);

        assert_eq!(pre_condition, post_condition);
    }

    #[test]
    fn test_should_do_nothing() {
        let mut pre_condition = ExprKind::If(Box::new(If::new(
            ExprKind::Atom(Atom::new(SyntaxObject::default(BooleanLiteral(true)))),
            ExprKind::Atom(Atom::new(SyntaxObject::default(BooleanLiteral(true)))),
            ExprKind::If(Box::new(If::new(
                ExprKind::Atom(Atom::new(SyntaxObject::default(BooleanLiteral(false)))),
                atom_int(10),
                atom_int(20),
                SyntaxObject::default(If),
            ))),
            SyntaxObject::default(If),
        )));

        let post_condition = pre_condition.clone();

        let mut visitor = RenameIdentifiersVisitor::new(&[], &[]);
        visitor.visit(&mut pre_condition);
        assert_eq!(pre_condition, post_condition);
    }

    #[test]
    fn test_rename_define() {
        let mut pre_condition: ExprKind = Define::new(
            atom_identifier("applesauce"),
            atom_int(10),
            SyntaxObject::default(TokenType::Define),
        )
        .into();

        let post_condition: ExprKind = Define::new(
            atom_identifier("##applesauce"),
            atom_int(10),
            SyntaxObject::default(TokenType::Define),
        )
        .into();

        let mut visitor = RenameIdentifiersVisitor::new(&[], &[]);
        visitor.visit(&mut pre_condition);
        assert_eq!(pre_condition, post_condition);
    }

    #[test]
    fn test_rename_define_datum_syntax() {
        let mut pre_condition: ExprKind = Define::new(
            List::new(thin_vec![
                atom_identifier("datum->syntax"),
                atom_identifier("escaping-definition"),
            ])
            .into(),
            atom_int(1),
            SyntaxObject::default(TokenType::Define),
        )
        .into();

        let post_condition: ExprKind = Define::new(
            List::new(thin_vec![
                atom_identifier("datum->syntax"),
                atom_identifier("escaping-definition"),
            ])
            .into(),
            atom_int(1),
            SyntaxObject::default(TokenType::Define),
        )
        .into();

        let mut visitor = RenameIdentifiersVisitor::new(&[], &[]);
        visitor.visit(&mut pre_condition);
        assert_eq!(pre_condition, post_condition);
    }
}
