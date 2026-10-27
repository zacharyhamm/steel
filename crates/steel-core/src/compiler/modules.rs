use crate::{
    compiler::{
        passes::{analysis::SemanticAnalysis, VisitorMutRefUnit},
        program::PROVIDE,
    },
    parser::{
        ast::{Atom, Begin, Define, ExprKind, List, Quote},
        expand_visitor::{
            expand_kernel_in_env, expand_kernel_in_env_with_change, is_begin_head,
            is_marked_native_head, native_binding_name, predeclare_native_definitions,
            prepare_native_globals, ExpanderMany, GlobalMap, RequiredMacroMap,
        },
        interner::InternedString,
        kernel::Kernel,
        parser::{
            lower_entire_ast, lower_macro_and_require_definitions, ParseError, Parser, Sources,
            SyntaxObject,
        },
        tokens::TokenType,
    },
    steel_vm::{
        engine::{default_prelude_macros, ModuleContainer},
        transducers::interleave,
    },
};
use crate::{parser::expand_visitor::Expander, rvals::Result};

use compact_str::CompactString;
use crossbeam_channel::Sender;
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use rustc_hash::{FxHashMap, FxHashSet};
// use smallvec::SmallVec;
use steel_parser::{ast::PROTO_HASH_GET, expr_list, parser::SourceId, span::Span};

use thin_vec::{thin_vec, ThinVec};

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    io::Read,
    path::PathBuf,
    sync::Arc,
};

use crate::parser::expander::SteelMacro;
use crate::stop;

use crate::time::SystemTime;

use crate::parser::expand_visitor::{
    expand, expand_module_scoped, expand_with_literal_globals, extract_macro_defs,
};

use super::{
    compiler::KernelDefMacroSpec,
    passes::{
        analysis::is_a_builtin_definition,
        begin::FlattenBegin,
        mangle::{collect_define_syntax, collect_defines, collect_globals, NameMangler},
    },
    program::{DEFINE_VALUES, FOR_SYNTAX, ONLY_IN, PREFIX_IN, REQUIRE_IDENT_SPEC, STRUCT_KEYWORD},
};

macro_rules! time {
    ($label:expr, $e:expr) => {{
        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        let e = $e;

        #[cfg(feature = "profiling")]
        log::debug!(target: "pipeline_time", "{}: {:?}", $label, now.elapsed());

        e
    }};
}

macro_rules! declare_builtins {
    ( $( $name:expr => $path:expr ), *) => {
        pub static BUILT_INS: &[(&str, &str)] = &[
            $( ($name, include_str!($path)), )*
        ];

        // TODO: Why was this an issue? Bugs with static string internment issues?
        pub(crate) fn intern_modules() {
            $(
                let _ = InternedString::from($name);
                let _ = InternedString::from($path);
            )*
        }
    };
}

pub(crate) const MANGLER_SEPARATOR: &str = "__%#__";

macro_rules! create_prelude {
    (
        $( $module:literal, )*
        $( for_syntax $module_for_syntax:literal ),*
    ) => {
        pub static PRELUDE_MODULES: &[&str] = &[
            $( $module, )*
            $( $module_for_syntax, )*
        ];

        pub static PRELUDE_WITHOUT_BASE: &str = concat!(
            $( "(require \"", $module, "\")\n", )*
            $( "(require (for-syntax \"", $module_for_syntax, "\"))\n", )*
        );

        pub static PRELUDE_STRING: &str = concat!(
            "(require-builtin steel/base)\n",
            $( "(require \"", $module, "\")\n", )*
            $( "(require (for-syntax \"", $module_for_syntax, "\"))\n", )*
        );
    }
}

// TODO: These need to be set up and interned in a stable position.
declare_builtins!(
    "steel/option" => "../scheme/modules/option.scm",
    "steel/result" => "../scheme/modules/result.scm",
    "steel/iterators" => "../scheme/modules/iterators.scm",
    "steel/async" => "../scheme/modules/async.scm",
    "steel/sync" => "../scheme/modules/sync.scm",
    "#%private/steel/contract" => "../scheme/modules/contracts.scm",
    "#%private/steel/print" => "../scheme/print.scm",
    "#%private/steel/ports" => "../scheme/modules/ports.scm",
    "#%private/steel/control" => "../scheme/modules/parameters.scm",
    "#%private/steel/reader" => "../scheme/modules/reader.scm",
    "#%private/steel/stdlib" => "../scheme/stdlib.scm",
    "#%private/steel/match" => "../scheme/modules/match.scm",
    "#%private/steel/sort" => "../scheme/modules/sort.scm",
    "steel/serde" => "../scheme/modules/serde.scm"
);

create_prelude!(
    "#%private/steel/stdlib",
    "#%private/steel/control",
    "#%private/steel/contract",
    "#%private/steel/print",
    "#%private/steel/ports",
    "#%private/steel/reader",
    "#%private/steel/match",
    "#%private/steel/sort",
    for_syntax "#%private/steel/control",
    for_syntax "#%private/steel/contract"
);

/// Takes a fully qualified path, and resolves it to a relative path,
/// for use in determining a unique module name irrespective of where the
/// module was loaded.
pub(crate) fn fully_qualified_to_relative(
    path: PathBuf,
    search_dirs: &[PathBuf],
) -> std::io::Result<PathBuf> {
    // First, check if the path is relative:
    let working_dir = std::env::current_dir()?;

    if let Ok(p) = path.strip_prefix(&working_dir) {
        if p.exists() {
            return Ok(p.to_path_buf());
        }
    }

    for p in search_dirs {
        if let Ok(p) = p.strip_prefix(&working_dir) {
            if p.exists() {
                return Ok(p.to_path_buf());
            }
        }
    }

    Ok(path)
}

#[cfg(not(target_family = "wasm"))]
pub static STEEL_SEARCH_PATHS: Lazy<Option<Vec<PathBuf>>> = Lazy::new(|| {
    std::env::var("STEEL_SEARCH_PATHS")
        .ok()
        .map(|x| std::env::split_paths(x.as_str()).collect::<Vec<_>>())
});

pub fn steel_search_dirs() -> Vec<PathBuf> {
    #[cfg(not(target_family = "wasm"))]
    return STEEL_SEARCH_PATHS.clone().unwrap_or_default();

    #[cfg(target_family = "wasm")]
    return Vec::new();
}

#[cfg(not(target_family = "wasm"))]
pub static STEEL_HOME: Lazy<Option<String>> = Lazy::new(|| {
    std::env::var("STEEL_HOME").ok().or_else(|| {
        let home = env_home::env_home_dir().map(|x| x.join(".steel"));

        if let Some(home) = home {
            if home.exists() {
                return Some(home.into_os_string().into_string().unwrap());
            }

            #[cfg(target_os = "windows")]
            {
                if let Err(e) = std::fs::create_dir(&home) {
                    eprintln!("Unable to create steel home directory {:?}: {}", home, e)
                }

                return Some(home.into_os_string().into_string().unwrap());
            }
        }

        #[cfg(not(target_os = "windows"))]
        {
            let bd = xdg::BaseDirectories::new();
            let home = bd.data_home;

            home.map(|mut x: PathBuf| {
                x.push("steel");

                // Just go ahead and initialize the directory, even though
                // this is probably not the best place to do this. This almost
                // assuredly could be lifted out of this check since failing here
                // could cause some annoyance.
                if !x.exists() {
                    if let Err(e) = std::fs::create_dir(&x) {
                        eprintln!("Unable to create steel home directory {:?}: {}", x, e)
                    }
                }

                x.into_os_string().into_string().unwrap()
            })
        }

        #[cfg(target_os = "windows")]
        None
    })
});

#[cfg(target_family = "wasm")]
pub static STEEL_HOME: Lazy<Option<String>> = Lazy::new(|| None);

pub fn steel_home() -> Option<String> {
    STEEL_HOME.clone()
}

/// Manages the modules
/// keeps some visited state on the manager for traversal
/// Also keeps track of the metadata for each file in order to determine
/// if it needs to be recompiled
#[derive(Clone)]
pub struct ModuleManager {
    pub(crate) compiled_modules: CompiledModuleCache,
    pub(crate) file_metadata: crate::HashMap<PathBuf, SystemTime>,
    visited: FxHashSet<PathBuf>,
    custom_builtins: HashMap<String, String>,
    rollback_metadata: crate::HashMap<PathBuf, SystemTime>,
    // #[serde(skip_serializing, skip_deserializing)]
    module_resolvers: Vec<Arc<dyn SourceModuleResolver>>,

    prelude_string: Cow<'static, str>,
}

pub trait SourceModuleResolver: Send + Sync {
    fn resolve(&self, key: &str) -> Option<String>;
    fn exists(&self, key: &str) -> bool;
}

impl ModuleManager {
    pub(crate) fn new(
        compiled_modules: crate::HashMap<PathBuf, CompiledModule>,
        file_metadata: crate::HashMap<PathBuf, SystemTime>,
    ) -> Self {
        ModuleManager {
            compiled_modules: CompiledModuleCache::new(compiled_modules),
            file_metadata,
            visited: FxHashSet::default(),
            custom_builtins: HashMap::new(),
            rollback_metadata: crate::HashMap::new(),
            module_resolvers: Vec::new(),
            prelude_string: Cow::Borrowed(PRELUDE_STRING),
        }
    }

    pub fn add_builtin_module(&mut self, module_name: String, mut text: String) {
        // Custom external builtins should be loaded with the prelude first, otherwise
        // they'll need to handle a bunch of imports
        text.insert_str(0, &self.prelude_string);

        self.custom_builtins.insert(module_name, text);
    }

    pub fn modules(&self) -> &crate::HashMap<PathBuf, CompiledModule> {
        &self.compiled_modules.compiled_modules
    }

    pub fn modules_mut(&mut self) -> &mut crate::HashMap<PathBuf, CompiledModule> {
        &mut self.compiled_modules.compiled_modules
    }

    pub(crate) fn default() -> Self {
        Self::new(crate::HashMap::default(), crate::HashMap::default())
    }

    pub fn set_prelude_string(&mut self, prelude_string: Cow<'static, str>) {
        self.prelude_string = prelude_string;
    }

    pub fn use_default_prelude_string(&mut self) {
        self.prelude_string = Cow::Borrowed(PRELUDE_STRING);
    }

    pub(crate) fn register_module_resolver(
        &mut self,
        resolver: impl SourceModuleResolver + 'static,
    ) {
        self.module_resolvers.push(Arc::new(resolver));
    }

    // Add the module directly to the compiled module cache
    pub(crate) fn add_module(
        &mut self,
        path: PathBuf,
        global_macro_map: &mut FxHashMap<InternedString, SteelMacro>,
        kernel: &mut Option<Kernel>,
        sources: &mut Sources,
        builtin_modules: ModuleContainer,
        global_bindings: GlobalMap,
    ) -> Result<()> {
        self.visited.clear();

        // TODO: Expand macros on the fly when visiting a module. Don't wait till the end
        // Macro expansion should happen as we enter a module.
        let mut module_builder = ModuleBuilder::new_from_path(
            path,
            &mut self.compiled_modules,
            &mut self.visited,
            &mut self.file_metadata,
            sources,
            kernel,
            builtin_modules,
            global_macro_map,
            global_bindings,
            &self.custom_builtins,
            &[],
            &self.module_resolvers,
            &self.prelude_string,
        )?;

        module_builder.compile()?;

        Ok(())
    }

    pub(crate) fn rollback_metadata(&mut self) {
        self.file_metadata = self.rollback_metadata.clone();
    }

    // #[allow(unused)]
    pub(crate) fn compile_main(
        &mut self,
        global_macro_map: &mut FxHashMap<InternedString, SteelMacro>,
        kernel: &mut Option<Kernel>,
        sources: &mut Sources,
        mut exprs: Vec<ExprKind>,
        path: Option<PathBuf>,
        builtin_modules: ModuleContainer,
        lifted_kernel_environments: &mut HashMap<String, KernelDefMacroSpec>,
        lifted_macro_environments: &mut HashMap<PathBuf, HashSet<InternedString>>,
        search_dirs: &[PathBuf],
        global_map: &FxHashMap<InternedString, usize>,
    ) -> Result<(Vec<ExprKind>, usize)> {
        // Wipe the visited set on entry
        self.visited.clear();

        self.rollback_metadata = self.file_metadata.clone();

        // TODO
        // This is also explicitly wrong -> we should separate the global macro map from the macros found locally in this module
        // For instance, (cond) is global, but (define-syntax blagh) might be local to main
        // if a module then defines a function (blagh) that is used inside its scope, this would expand the macro in that scope
        // which we do not want
        let mut program_macros = exprs
            .iter()
            .filter_map(|expr| match expr {
                ExprKind::Macro(m) => m.name.atom_identifier().copied(),
                _ => None,
            })
            .collect::<FxHashSet<_>>();
        extract_macro_defs(&mut exprs, global_macro_map, global_map)?;

        let no_kernel = kernel.is_none();
        let mut pending_globals = collect_globals(&exprs);
        let mut literal_globals = pending_globals.clone();
        // Whether a known binding shadows a native head; set by every literal refresh.
        let mut native_heads_shadowed = true;
        // Without a kernel, main's expansion updates the global macros while modules compile
        // against them, so required modules see a snapshot. Without requires, none compile.
        let no_macros = FxHashMap::default();
        let discovery_macro_map;
        let module_macro_map;
        let mut module_builder = ModuleBuilder::main(
            path,
            exprs,
            &mut self.compiled_modules,
            &mut self.visited,
            &mut self.file_metadata,
            sources,
            kernel,
            builtin_modules.clone(),
            &no_macros,
            GlobalMap::Map(global_map),
            &self.custom_builtins,
            search_dirs,
            &self.module_resolvers,
            &self.prelude_string,
        )?;

        if no_kernel {
            module_builder.collect_requires()?;
            let mut exclusions = HashSet::new();
            let mut imported_macros = FxHashSet::default();
            let mut shadowed = FxHashSet::default();
            let mut refresh_literals = true;
            if !module_builder.require_objects.is_empty() {
                discovery_macro_map = global_macro_map
                    .iter()
                    .filter(|(name, _)| !pending_globals.contains(name))
                    .map(|(name, value)| (*name, value.clone()))
                    .collect::<FxHashMap<_, _>>();
                module_builder.global_macro_map = &discovery_macro_map;
                module_builder.predeclare_imports(
                    &mut pending_globals,
                    &mut exclusions,
                    &mut imported_macros,
                )?;
                let shapes = flatten_main_begins(&mut module_builder.source_ast)?;
                // Keep these expansions: required modules must see the bindings they introduce.
                for index in 0..module_builder.source_ast.len() {
                    if refresh_literals {
                        literal_globals = refresh_main_literals(
                            &module_builder.source_ast,
                            global_macro_map,
                            &program_macros,
                            global_map,
                            &pending_globals,
                            &imported_macros,
                            &builtin_modules,
                        );
                        native_heads_shadowed = shadows_any_native_head(&literal_globals);
                    }
                    let mut expander = Expander::new(
                        global_macro_map,
                        &exclusions,
                        GlobalMap::Layered(global_map, &pending_globals),
                    );
                    // Imported macros expand later and may quote or bind their arguments.
                    expander.deferred_macros = Some(&imported_macros);
                    expander.literal_globals = GlobalMap::Layered(global_map, &literal_globals);
                    let expr = &mut module_builder.source_ast[index];
                    let is_macro = |name: &InternedString| {
                        global_macro_map.contains_key(name) || imported_macros.contains(name)
                    };
                    let previous_bindings = collect_main_literal_bindings(
                        std::slice::from_ref(expr),
                        global_map,
                        &pending_globals,
                        &is_macro,
                        &builtin_modules,
                    );
                    expander.expand(expr)?;
                    let bindings = collect_main_literal_bindings(
                        std::slice::from_ref(expr),
                        global_map,
                        &pending_globals,
                        &is_macro,
                        &builtin_modules,
                    );
                    let changed;
                    (refresh_literals, changed) = update_main_literals(
                        expr,
                        &previous_bindings,
                        &bindings,
                        native_heads_shadowed,
                        &mut pending_globals,
                        &mut literal_globals,
                    );
                    collect_defines(std::slice::from_ref(expr), &mut |name| {
                        shadowed.insert(name);
                        exclusions.insert(name);
                        refresh_literals |= imported_macros.remove(&name);
                    });
                    if changed && !refresh_literals {
                        bind_program_literals(
                            global_macro_map,
                            &program_macros,
                            global_map,
                            &literal_globals,
                        );
                    }
                }
                regroup_main_begins(&mut module_builder.source_ast, shapes);
            }
            if refresh_literals {
                literal_globals = refresh_main_literals(
                    &module_builder.source_ast,
                    global_macro_map,
                    &program_macros,
                    global_map,
                    &pending_globals,
                    &imported_macros,
                    &builtin_modules,
                );
            }
            if !module_builder.require_objects.is_empty() {
                module_macro_map = global_macro_map
                    .iter()
                    .filter(|(name, _)| !shadowed.contains(name))
                    .map(|(name, value)| (*name, value.clone()))
                    .collect::<FxHashMap<_, _>>();
                module_builder.global_macro_map = &module_macro_map;
            }
        } else {
            module_builder.global_macro_map = global_macro_map;
        }
        module_builder.global_bindings = GlobalMap::Layered(global_map, &literal_globals);
        let mut module_statements = module_builder.compile()?;
        let compiled_module_count = module_statements.len();

        module_builder.collect_provides()?;

        let mut ast = core::mem::take(&mut module_builder.source_ast);

        let mut require_defines = Vec::new();

        let mut explicit_requires = HashMap::new();

        for require_object in &module_builder.require_objects {
            let path = require_object.path.get_path();
            explicit_requires.clear();

            // If there _are_ explicit identifiers to import, limit what we import to what
            // is in the set
            for ident in &require_object.idents_to_import {
                match ident {
                    MaybeRenamed::Normal(i) => {
                        explicit_requires.insert(i.atom_identifier().unwrap().clone(), None);
                    }

                    MaybeRenamed::Renamed(from, to) => {
                        explicit_requires.insert(
                            from.atom_identifier().unwrap().clone(),
                            Some(to.atom_identifier().unwrap().clone()),
                        );
                    }
                }
            }

            // println!("{:?}", path);
            let module = if let Some(module) = module_builder
                .compiled_modules
                .get(path.as_ref(), module_builder.sources)
            {
                module
            } else {
                // log::debug!(target: "modules", "No provides found for module, skipping: {:?}", path);

                continue;
            };

            for provide_expr in &module.provides {
                // For whatever reason, the value coming into module.provides is an expression like: (provide expr...)
                for provide in &provide_expr.list().unwrap().args[1..] {
                    let other_module_prefix = module.prefix();

                    // TODO: Expand the contract out into something we expect
                    // Otherwise, this is going to blow up
                    match provide {
                        ExprKind::List(l) => {
                            if let Some(qualifier) = l.first_ident() {
                                match *qualifier {
                                    x if x == *REQUIRE_IDENT_SPEC => {
                                        // Directly expand into define/contract, but with the value just being the hash get below

                                        // (bind/c contract name 'name)

                                        let name = l.args.get(1).unwrap();

                                        if !explicit_requires.is_empty()
                                            && !name
                                                .atom_identifier()
                                                .map(|x| explicit_requires.contains_key(x))
                                                .unwrap_or_default()
                                        {
                                            continue;
                                        }

                                        if module
                                            .macro_map
                                            .contains_key(name.atom_identifier().unwrap())
                                        {
                                            continue;
                                        }

                                        let hash_get = expr_list![
                                            ExprKind::atom(*PROTO_HASH_GET),
                                            ExprKind::atom(
                                                CompactString::new(MODULE_PREFIX)
                                                    + &other_module_prefix
                                            ),
                                            ExprKind::Quote(Box::new(Quote::new(
                                                name.clone(),
                                                SyntaxObject::default(TokenType::Quote)
                                            ))),
                                        ];

                                        let mut owned_name = name.clone();

                                        // If we have the alias listed, we should use it
                                        if !explicit_requires.is_empty() {
                                            if let Some(alias) = explicit_requires
                                                .get(name.atom_identifier().unwrap())
                                                .copied()
                                                .flatten()
                                            {
                                                *owned_name.atom_identifier_mut().unwrap() =
                                                    alias.clone();
                                            }
                                        }

                                        if let Some(prefix) = &require_object.prefix {
                                            if let Some(existing) = owned_name.atom_identifier_mut()
                                            {
                                                let mut prefixed_identifier = prefix.clone();
                                                prefixed_identifier.push_str(existing.resolve());

                                                // Update the existing identifier to point to a new one with the prefix applied
                                                *existing = prefixed_identifier.into();
                                            }
                                        }

                                        let define = ExprKind::Define(Box::new(Define::new(
                                            owned_name,
                                            hash_get,
                                            SyntaxObject::default(TokenType::Define),
                                        )));

                                        require_defines.push(define);
                                    }
                                    _ => {
                                        stop!(TypeMismatch => format!("provide expects either an identifier, (for-syntax <ident>), or (contract/out ...), found: {}", provide))
                                    }
                                }
                            } else {
                                stop!(TypeMismatch => "provide expects either an identifier or a (for-syntax <ident>)")
                            }
                        }
                        ExprKind::Atom(_) => {
                            if !explicit_requires.is_empty()
                                && !provide
                                    .atom_identifier()
                                    .map(|x| explicit_requires.contains_key(x))
                                    .unwrap_or_default()
                            {
                                continue;
                            }

                            if module
                                .macro_map
                                .contains_key(provide.atom_identifier().unwrap())
                            {
                                continue;
                            }

                            let hash_get = expr_list![
                                ExprKind::atom(*PROTO_HASH_GET),
                                ExprKind::atom(
                                    CompactString::new(MODULE_PREFIX) + &other_module_prefix
                                ),
                                ExprKind::Quote(Box::new(Quote::new(
                                    provide.clone(),
                                    SyntaxObject::default(TokenType::Quote)
                                ))),
                            ];

                            let mut owned_provide = provide.clone();

                            // If we have the alias listed, we should use it
                            if !explicit_requires.is_empty() {
                                if let Some(alias) = explicit_requires
                                    .get(provide.atom_identifier().unwrap())
                                    .copied()
                                    .flatten()
                                {
                                    *owned_provide.atom_identifier_mut().unwrap() = alias.clone();
                                }
                            }

                            // TODO: If there is a prefix applied, use it here?
                            if let Some(prefix) = &require_object.prefix {
                                // println!("Found prefix: {}", prefix);

                                if let Some(existing) = owned_provide.atom_identifier_mut() {
                                    let mut prefixed_identifier = prefix.clone();
                                    prefixed_identifier.push_str(existing.resolve());

                                    // Update the existing identifier to point to a new one with the prefix applied
                                    *existing = prefixed_identifier.into();
                                }
                            }

                            let define = ExprKind::Define(Box::new(Define::new(
                                owned_provide,
                                hash_get,
                                SyntaxObject::default(TokenType::Define),
                            )));

                            require_defines.push(define);
                        }
                        _ => {
                            stop!(TypeMismatch => "provide expression needs to either be a `contract/out` form or an identifier")
                        }
                    }
                }
            }
        }

        let mut mangled_asts = Vec::with_capacity(ast.len());

        let require_objects = core::mem::take(&mut module_builder.require_objects);
        drop(module_builder);

        // TODO: Move this to the lower level as well
        // It seems we're only doing this expansion at the top level, but we _should_ do this at the lower level as well
        for require_object in require_objects.iter()
        // .filter(|x| x.for_syntax)
        // .map(|x| x.path.get_path())
        {
            let require_for_syntax = require_object.path.get_path();

            let (module, in_scope_macros, mut name_mangler) = Self::find_in_scope_macros(
                &mut self.compiled_modules,
                require_for_syntax.as_ref(),
                require_object,
                &mut mangled_asts,
            );

            // let kernel_macros_in_scope: HashSet<_> =
            //     module.provides_for_syntax.iter().cloned().collect();

            // let defmacros_exported: HashSet<_> = module.

            // dbg!(&kernel_macros_in_scope);

            let module_name = module.name.to_str().unwrap().to_string();
            // Built on the first expansion that needs it, since most requires expand nothing.
            let mut native_globals: Option<FxHashSet<InternedString>> = None;

            if let Some(kernel) = kernel.as_mut() {
                if kernel.exported_defmacros(&module_name).is_some() {
                    lifted_kernel_environments.insert(
                        module_name.clone(),
                        KernelDefMacroSpec {
                            _env: module_name.clone(),
                            _exported: None,
                            name_mangler: name_mangler.clone(),
                        },
                    );
                }
            }

            for expr in ast.iter_mut() {
                // @matt 12/8/2023
                // The easiest thing to do here, is to go to the other module, and find
                // what defmacros have been exposed on the require for syntax. Once those
                // have been found, we run a pass with kernel expansion, limiting the
                // expander to only use the macros that we've exposed. After that,
                // we run the expansion again, using the full suite of defmacro capabilities.
                //
                // The question that remains - how to define the neat phases of what kinds
                // of macros can expand into what? Can defmacro -> syntax-rules -> defmacro?
                // This could eventually prove to be cumbersome, but it is still early
                // for defmacro. Plus, I need to create a syntax-case or syntax-parse
                // frontend before the defmacro style macros become too pervasive.
                //
                // TODO: Replicate this behavior over to builtin modules

                let exclusions = HashSet::new();

                // First expand the in scope macros
                // These are macros
                let mut expander = Expander::new(
                    &in_scope_macros,
                    &exclusions,
                    GlobalMap::Set(&name_mangler.globals),
                );
                expander.native_struct_templates = !module.macro_map.contains_key(&*STRUCT_KEYWORD)
                    && !global_macro_map.contains_key(&*STRUCT_KEYWORD);
                expander.expand(expr)?;
                let changed = false;

                if expander.changed || changed {
                    let _source_id = sources.get_source_id(&module.name).unwrap();

                    // let mut fully_expanded = first_round_expanded;

                    expand(
                        expr,
                        &module.macro_map,
                        GlobalMap::Set(&name_mangler.globals), // source_id,
                    )?;

                    // Expanding the kernel with only these macros...
                    let changed = expand_kernel_in_env_with_change(
                        expr,
                        kernel.as_mut(),
                        // We don't need to expand those here
                        ModuleContainer::default(),
                        &module_name,
                        if no_kernel {
                            GlobalMap::Layered(
                                global_map,
                                native_globals.get_or_insert_with(|| {
                                    let mut globals = name_mangler.globals.clone();
                                    globals.extend(pending_globals.iter().copied());
                                    globals
                                }),
                            )
                        } else {
                            GlobalMap::Set(&name_mangler.globals)
                        },
                    )?;

                    // Without a kernel, `changed` only reports native lowering of main's own
                    // forms, and imported templates are already mangled, so mangling here would
                    // capture main's references to the provider's private names.
                    if changed && !no_kernel {
                        name_mangler.visit(expr);
                    }
                }
            }

            // Global macro map - also need to expand with ALL macros
            // post expansion in the target environment, which means we can't _just_
            // extend the global macro map with the target in scope macros, we need to
            // do something like the two pass expansion
            program_macros.retain(|name| !in_scope_macros.contains_key(name));
            global_macro_map.extend(in_scope_macros);

            lifted_macro_environments.insert(module.name.clone(), Default::default());
        }

        // Include the defines from the modules now imported
        module_statements.append(&mut require_defines);

        let main_start = module_statements.len();
        let shapes = if no_kernel {
            Some(flatten_main_begins(&mut ast)?)
        } else {
            None
        };
        module_statements.append(&mut ast);

        let mut refresh_literals = true;
        time!("Top level macro evaluation time", {
            // Kernel-backed modules may still need prelude macros, but must not see main's macros.
            if !no_kernel {
                let prelude_macros = default_prelude_macros();
                for expr in &mut module_statements[..compiled_module_count] {
                    expand(expr, &prelude_macros, GlobalMap::Map(global_map))?;
                }
            }

            for index in compiled_module_count..module_statements.len() {
                if no_kernel && refresh_literals {
                    literal_globals = refresh_main_literals(
                        &module_statements[compiled_module_count..],
                        global_macro_map,
                        &program_macros,
                        global_map,
                        &pending_globals,
                        &FxHashSet::default(),
                        &builtin_modules,
                    );
                    native_heads_shadowed = shadows_any_native_head(&literal_globals);
                }
                let expr = &mut module_statements[index];
                let previous_bindings = no_kernel.then(|| {
                    collect_main_literal_bindings(
                        std::slice::from_ref(expr),
                        global_map,
                        &pending_globals,
                        &|name| global_macro_map.contains_key(name),
                        &builtin_modules,
                    )
                });
                let globals = if no_kernel {
                    GlobalMap::Layered(global_map, &pending_globals)
                } else {
                    GlobalMap::Map(global_map)
                };
                let (found_in_scope, expanded) = expand_with_literal_globals(
                    expr,
                    global_macro_map,
                    globals,
                    if no_kernel {
                        GlobalMap::Layered(global_map, &literal_globals)
                    } else {
                        globals
                    },
                )?;
                refresh_literals = false;

                let mut changed = false;
                // An unchanged statement's bindings and definitions are already recorded.
                if let Some(previous_bindings) = previous_bindings.filter(|_| expanded) {
                    let bindings = collect_main_literal_bindings(
                        std::slice::from_ref(expr),
                        global_map,
                        &pending_globals,
                        &|name| global_macro_map.contains_key(name),
                        &builtin_modules,
                    );
                    (refresh_literals, changed) = update_main_literals(
                        expr,
                        &previous_bindings,
                        &bindings,
                        native_heads_shadowed,
                        &mut pending_globals,
                        &mut literal_globals,
                    );
                }
                for item in found_in_scope.iter() {
                    refresh_literals |= global_macro_map.remove(item).is_some();

                    for (_, shadowed_vars) in lifted_macro_environments.iter_mut() {
                        // If this was recently shadowed, then we don't want it any more.
                        shadowed_vars.insert(*item);
                    }
                }
                if changed && !refresh_literals {
                    bind_program_literals(
                        global_macro_map,
                        &program_macros,
                        global_map,
                        &literal_globals,
                    );
                }
            }
        });

        if no_kernel && refresh_literals {
            refresh_main_literals(
                &module_statements[compiled_module_count..],
                global_macro_map,
                &program_macros,
                global_map,
                &pending_globals,
                &FxHashSet::default(),
                &builtin_modules,
            );
        }
        if let Some(shapes) = shapes {
            let mut main_statements = module_statements.split_off(main_start);
            regroup_main_begins(&mut main_statements, shapes);
            module_statements.append(&mut main_statements);
        }
        Ok((module_statements, compiled_module_count))
    }

    fn find_in_scope_macros<'a>(
        compiled_modules: &'a mut CompiledModuleCache,
        require_for_syntax: &'a PathBuf,
        require_object: &'a RequireObject,
        mangled_asts: &'a mut Vec<ExprKind>,
    ) -> (
        &'a CompiledModule,
        FxHashMap<InternedString, SteelMacro>,
        NameMangler,
    ) {
        let module = compiled_modules
            .compiled_modules
            .get(require_for_syntax)
            .unwrap_or_else(|| panic!("Module missing!: {:?}", require_for_syntax));

        let prefix = module.prefix();

        // Only runtime bindings need module prefixes; macro names remain expandable.
        let mut globals = collect_globals(&module.ast);
        for require in &module.require_objects {
            let imported = &compiled_modules.compiled_modules[require.path.get_path().as_ref()];
            imported_bindings(
                require,
                &imported.provides,
                &imported.provides_for_syntax,
                &imported.macro_map,
                |name, smacro| {
                    if smacro.is_none() {
                        globals.insert(name);
                    }
                },
            );
        }

        let module = compiled_modules
            .compiled_modules
            .get_mut(require_for_syntax)
            .unwrap_or_else(|| panic!("Module missing!: {:?}", require_for_syntax));

        let mut name_mangler = NameMangler::new(globals, prefix);

        // If the module hasn't been emitted already, then include it here
        if !module.emitted {
            let mut module_ast = module.ast.clone();

            name_mangler.mangle_vars(&mut module_ast);

            mangled_asts.append(&mut module_ast);
        }

        {
            let mut should_mangle = false;
            for (_, smacro) in module.macro_map.iter() {
                if !smacro.special_mangled && !smacro.is_mangled() {
                    should_mangle = true;
                    break;
                }
            }

            if should_mangle {
                for (_, smacro) in Arc::make_mut(&mut module.macro_map).iter_mut() {
                    if !smacro.special_mangled && !smacro.is_mangled() {
                        name_mangler.mangle_macro(smacro);
                        smacro.mark_mangled();
                    }
                }
            }
        }

        // let provided_macros = module.provides_for
        // let expander = Expander::new(&module.macro_map);
        // TODO
        // expand expressions one by one
        // if expansion with _just_ public macros from the required module doesn't do anything, stop
        // if it _does_ change, do another pass with all of the macros in scope
        // do this for each of the expressions in the file in this loop
        // TODO -> try not cloning this
        // TODO -> do this in the module expansion as well
        let mut in_scope_macros = FxHashMap::default();
        imported_bindings(
            require_object,
            &module.provides,
            &module.provides_for_syntax,
            &module.macro_map,
            |name, smacro| {
                if let Some(smacro) = smacro {
                    in_scope_macros.insert(name, smacro.clone());
                }
            },
        );

        (module, in_scope_macros, name_mangler)
    }
}

// Pre-compile module to bytecode? Is it even possible?
// Dynamically linking the module would then make it relatively
// easy to just load everything up at the start.
// Compiled module _should_ be possible now. Just create a target
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CompiledModule {
    name: PathBuf,
    provides: Vec<ExprKind>,
    require_objects: Vec<RequireObject>,
    provides_for_syntax: Vec<InternedString>,
    pub(crate) macro_map: Arc<FxHashMap<InternedString, SteelMacro>>,
    pub(crate) ast: Vec<ExprKind>,
    emitted: bool,
    cached_prefix: CompactString,
    downstream: Vec<PathBuf>,
    downstream_builtins: Vec<PathBuf>,

    pub(crate) compiled_ast: Option<ExprKind>,
}

pub static MANGLER_PREFIX: &str = "##mm";
pub(crate) const MACRO_MANGLE_PREFIX: &str = "##macro-";
pub static MODULE_PREFIX: &str = "__module-";
pub static MANGLED_MODULE_PREFIX: &str = "__module-##mm";

pub fn path_to_prefix_name(name: PathBuf) -> String {
    let mut base = CompactString::new(MANGLER_PREFIX);

    if let Some(steel_home) = STEEL_HOME.as_ref() {
        // Intern this?
        let name = name
            .to_str()
            .unwrap()
            .trim_start_matches(steel_home.as_str());

        let interned = InternedString::from_str(name);
        let id = interned.get().into_inner();

        base.push_str(&id.to_string());
        base.push_str(MANGLER_SEPARATOR);
    } else {
        let interned = InternedString::from_str(name.to_str().unwrap());
        let id = interned.get().into_inner();

        base.push_str(&id.to_string());
        base.push_str(MANGLER_SEPARATOR);
    }

    base.into_string()
}

pub fn path_to_module_name(name: PathBuf) -> String {
    let mut base = CompactString::new(MANGLED_MODULE_PREFIX);

    if let Some(steel_home) = STEEL_HOME.as_ref() {
        // Intern this?
        let name = name
            .to_str()
            .unwrap()
            .trim_start_matches(steel_home.as_str());

        let interned = InternedString::from_str(name);
        let id = interned.get().into_inner();

        base.push_str(&id.to_string());
        base.push_str(MANGLER_SEPARATOR);
    } else {
        let interned = InternedString::from_str(name.to_str().unwrap());
        let id = interned.get().into_inner();

        base.push_str(&id.to_string());
        base.push_str(MANGLER_SEPARATOR);
    }

    base.into_string()
}

// TODO: @Matt 6/12/23 - This _should_ be serializable. If possible, we can try to store intermediate objects down to some file.
impl CompiledModule {
    pub fn new(
        name: PathBuf,
        provides: Vec<ExprKind>,
        require_objects: Vec<RequireObject>,
        provides_for_syntax: Vec<InternedString>,
        macro_map: Arc<FxHashMap<InternedString, SteelMacro>>,
        ast: Vec<ExprKind>,
        downstream: Vec<PathBuf>,
        downstream_builtins: Vec<PathBuf>,
    ) -> Self {
        let mut base = CompactString::new(MANGLER_PREFIX);

        if let Some(steel_home) = STEEL_HOME.as_ref() {
            // Intern this?
            let name = name
                .to_str()
                .unwrap()
                .trim_start_matches(steel_home.as_str());

            let interned = InternedString::from_str(name);
            let id = interned.get().into_inner();

            // base.push_str(name);
            base.push_str(&id.to_string());
            base.push_str(MANGLER_SEPARATOR);

            // println!("{}", base);
            // println!("Byte length: {}", base.len());
        } else {
            let interned = InternedString::from_str(name.to_str().unwrap());
            let id = interned.get().into_inner();

            // base.push_str(self.name.to_str().unwrap());
            base.push_str(&id.to_string());
            base.push_str(MANGLER_SEPARATOR);
        }

        Self {
            name,
            provides,
            require_objects,
            provides_for_syntax,
            macro_map,
            ast,
            emitted: false,
            cached_prefix: base,
            downstream,
            downstream_builtins,
            compiled_ast: None,
        }
    }

    // TODO: Should cache this
    pub fn prefix(&self) -> CompactString {
        self.cached_prefix.clone()
    }

    pub fn get_compiled_ast(&self) -> &Option<ExprKind> {
        &self.compiled_ast
    }

    pub fn get_macros(&self) -> Arc<FxHashMap<InternedString, SteelMacro>> {
        self.macro_map.clone()
    }

    pub fn get_ast(&self) -> &[ExprKind] {
        &self.ast
    }

    pub fn name(&self) -> &PathBuf {
        &self.name
    }

    pub fn get_provides(&self) -> &[ExprKind] {
        &self.provides
    }

    pub fn get_requires(&self) -> &[RequireObject] {
        &self.require_objects
    }

    // pub fn get_requires(&self) -> &[PathBuf] {
    //     &self.requires
    // }

    pub fn set_emitted(&mut self, emitted: bool) {
        self.emitted = emitted;
    }

    fn to_top_level_module(
        &mut self,
        modules: &crate::HashMap<PathBuf, CompiledModule>,
        global_macro_map: &FxHashMap<InternedString, SteelMacro>,
    ) -> Result<ExprKind> {
        let mut globals = collect_globals(&self.ast);

        let mut exprs = self.ast.clone();

        let mut provide_definitions = Vec::new();

        // TODO: Change this to not use the full path. Unfortunately that isn't portable,
        // so we should use something that is more agnostic of the target location
        // if we were to load.
        //
        // Probably a better idea would be to somehow assign a unique ID to each module;
        // the path from the $STEEL_HOME would be relatively safe. That way we can just strip
        // the $STEEL_HOME root away from the path if it starts with it, and then have
        // that resolve to be the "name" of the module.
        let prefix = self.prefix();

        // Now we should be able to set up a series of requires with the right style
        // ;; Refresh the module definition in this namespace
        // (define a-module.rkt-b (hash-get 'b b-module.rkt-b))

        let mut explicit_requires = HashMap::new();

        // TODO: This is the same as the top level, they should be merged
        for require_object in &self.require_objects {
            let path = require_object.path.get_path();

            explicit_requires.clear();

            for ident in &require_object.idents_to_import {
                match ident {
                    MaybeRenamed::Normal(i) => {
                        explicit_requires.insert(i.atom_identifier().unwrap().clone(), None);
                    }
                    MaybeRenamed::Renamed(from, to) => {
                        explicit_requires.insert(
                            from.atom_identifier().unwrap().clone(),
                            Some(to.atom_identifier().unwrap().clone()),
                        );
                    }
                }
            }

            // println!("{:?}", path);
            // println!("{:?}", modules.keys().collect::<Vec<_>>());
            let module = modules.get(path.as_ref()).unwrap();

            let other_module_prefix = module.prefix();

            for provide_expr in &module.provides {
                // For whatever reason, the value coming into module.provides is an expression like: (provide expr...)
                for provide in &provide_expr.list().unwrap().args[1..] {
                    match provide {
                        ExprKind::List(l) => {
                            if let Some(qualifier) = l.first_ident() {
                                if module.macro_map.contains_key(qualifier) {
                                    continue;
                                }

                                match *qualifier {
                                    x if x == *REQUIRE_IDENT_SPEC => {
                                        // Directly expand into define/contract, but with the value just being the hash get below

                                        // (bind/c contract name 'name)

                                        let name = l.args.get(1).unwrap();

                                        if !explicit_requires.is_empty()
                                            && !name
                                                .atom_identifier()
                                                .map(|x| explicit_requires.contains_key(x))
                                                .unwrap_or_default()
                                        {
                                            continue;
                                        }

                                        if module
                                            .macro_map
                                            .contains_key(name.atom_identifier().unwrap())
                                        {
                                            continue;
                                        }

                                        let hash_get = expr_list![
                                            ExprKind::atom(*PROTO_HASH_GET),
                                            ExprKind::atom(
                                                CompactString::new(MODULE_PREFIX)
                                                    + &other_module_prefix
                                            ),
                                            ExprKind::Quote(Box::new(Quote::new(
                                                name.clone(),
                                                SyntaxObject::default(TokenType::Quote)
                                            ))),
                                        ];

                                        let mut owned_name = name.clone();

                                        // If we have the alias listed, we should use it
                                        if !explicit_requires.is_empty() {
                                            if let Some(alias) = explicit_requires
                                                .get(name.atom_identifier().unwrap())
                                                .copied()
                                                .flatten()
                                            {
                                                *owned_name.atom_identifier_mut().unwrap() =
                                                    alias.clone();
                                            }
                                        }

                                        if let Some(prefix) = &require_object.prefix {
                                            if let Some(existing) = owned_name.atom_identifier_mut()
                                            {
                                                let mut prefixed_identifier = prefix.clone();
                                                prefixed_identifier.push_str(existing.resolve());

                                                // Update the existing identifier to point to a new one with the prefix applied
                                                *existing = prefixed_identifier.into();
                                            }
                                        }

                                        globals.insert(*name.atom_identifier().unwrap());

                                        let define = ExprKind::Define(Box::new(Define::new(
                                            owned_name,
                                            hash_get,
                                            SyntaxObject::default(TokenType::Define),
                                        )));

                                        provide_definitions.push(define);
                                    }

                                    _ => {
                                        stop!(TypeMismatch => format!("provide expects either an identifier, (for-syntax <ident>), or (contract/out ...) - found: {}", provide))
                                    }
                                }
                            } else {
                                stop!(TypeMismatch => "provide expects either an identifier or a (for-syntax <ident>)")
                            }
                        }
                        ExprKind::Atom(_) => {
                            if !explicit_requires.is_empty()
                                && !provide
                                    .atom_identifier()
                                    .map(|x| explicit_requires.contains_key(x))
                                    .unwrap_or_default()
                            {
                                continue;
                            }

                            if module
                                .macro_map
                                .contains_key(provide.atom_identifier().unwrap())
                            {
                                continue;
                            }

                            // Mangle with a prefix if necessary
                            let mut provide = provide.clone();
                            let raw_provide = provide.clone();

                            // If we have the alias listed, we should use it
                            if !explicit_requires.is_empty() {
                                if let Some(alias) = explicit_requires
                                    .get(provide.atom_identifier().unwrap())
                                    .copied()
                                    .flatten()
                                {
                                    *provide.atom_identifier_mut().unwrap() = alias.clone();
                                }
                            }

                            if let Some(prefix) = &require_object.prefix {
                                if let Some(existing) = provide.atom_identifier_mut() {
                                    let mut prefixed_identifier = prefix.clone();
                                    prefixed_identifier.push_str(existing.resolve());

                                    // Update the existing identifier to point to a new one with the prefix applied
                                    *existing = prefixed_identifier.into();
                                }
                            }

                            let provide_ident = provide.atom_identifier().unwrap();

                            // Since this is now bound to be in the scope of the current working module, we also want
                            // this to be mangled. In the event we do something like, qualify the import, then we might
                            // have to mangle this differently
                            globals.insert(*provide_ident);

                            let define = ExprKind::Define(Box::new(Define::new(
                                ExprKind::atom(prefix.clone() + provide_ident.resolve()),
                                expr_list![
                                    ExprKind::atom(*PROTO_HASH_GET),
                                    ExprKind::atom(
                                        CompactString::new(MODULE_PREFIX) + &other_module_prefix
                                    ),
                                    ExprKind::Quote(Box::new(Quote::new(
                                        raw_provide.clone(),
                                        SyntaxObject::default(TokenType::Quote)
                                    )))
                                ],
                                SyntaxObject::default(TokenType::Define),
                            )));

                            // if require_object.prefix.is_some() {
                            //     println!("{}", define);
                            // }

                            provide_definitions.push(define);
                        }
                        _ => {
                            stop!(TypeMismatch => "provide expression needs to either be a `contract/out` form or an identifier")
                        }
                    }
                }
            }
        }

        // Mangle all of the variables that are either:
        // 1. Defined locally in this file
        // 2. Required by another file
        let mut name_mangler = NameMangler::new(globals, prefix.clone());

        // Afterwards, walk through and unmangle any quoted values, since these
        // were intended to be used with non mangled values.
        // let name_unmangler = NameUnMangler::new(&prefix);

        name_mangler.mangle_vars(&mut exprs);

        // The provide definitions should also be mangled
        name_mangler.mangle_vars(&mut provide_definitions);

        // let mut hash_builder = Vec::new();

        // These are gonna be the pairs
        // hash_builder.push(());

        // Construct the series of provides as well, we'll want these to refer to the correct values
        //
        let mut provides: smallvec::SmallVec<[(ExprKind, ExprKind); 24]> = self
            .provides
            .iter()
            .flat_map(|x| &x.list().unwrap().args[1..])
            .cloned()
            .map(|x| (x.clone(), x))
            .collect();

        for provide in &mut provides {
            match &provide.1 {
                ExprKind::List(l) => {
                    if let Some(qualifier) = l.first_ident() {
                        match qualifier {
                            x if *x == *REQUIRE_IDENT_SPEC => {
                                // *provide = expand(l.get(2).unwrap().clone(), global_macro_map)?;

                                // *provide = expand(l.)

                                provide.0 = l.get(1).unwrap().clone();

                                let mut provide_expr = l.get(2).unwrap().clone();
                                expand(
                                    &mut provide_expr,
                                    global_macro_map,
                                    GlobalMap::Set(&name_mangler.globals),
                                )?;

                                provide.1 = provide_expr;

                                continue;

                                // name_unmangler.unmangle_expr(provide);
                            }
                            unknown => {
                                stop!(TypeMismatch => "bar provide expects either an identifier, (for-syntax <ident>), or (contract/out ...), found: {}", unknown)
                            }
                        }
                    } else {
                        stop!(TypeMismatch => "provide expects either an identifier or a (for-syntax <ident>)")
                    }
                }
                ExprKind::Atom(_) => {
                    continue;
                }
                _ => {
                    stop!(TypeMismatch => "provide expression needs to either be a `contract/out` form or an identifier")
                }
            }
        }

        // Drop all of the macro references here
        provides.retain(|x| !self.macro_map.contains_key(x.0.atom_identifier().unwrap()));

        // We want one without the mangled version, for the actual provides
        let un_mangled = provides.clone();

        let left_unmangled: Vec<_> = un_mangled.into_iter().map(|x| x.0).collect();

        let mut right: Vec<_> = provides.into_iter().map(|x| x.1).collect();

        name_mangler.mangle_vars(&mut right);
        // name_unmangler.unmangle_vars(&mut provides);

        let mut hash_body = thin_vec![ExprKind::ident("%proto-hash%")];

        // We can put the module name in there, but that doesn't help us get the docs out...
        // Probably need to just store the docs directly in the module itself as well?
        // hash_body.push(ExprKind::atom("#:module-name"));
        // hash_body.push(ExprKind::atom(prefix.clone()));

        // left_unmangled.pretty_print();

        hash_body.extend(interleave(
            left_unmangled.into_iter().map(|x| {
                if let ExprKind::Atom(_) = x {
                    ExprKind::Quote(Box::new(Quote::new(
                        x,
                        SyntaxObject::default(TokenType::Quote),
                    )))
                } else if let ExprKind::List(l) = x {
                    if let Some(qualifier) = l.first_ident() {
                        match qualifier {
                            x if *x == *REQUIRE_IDENT_SPEC => {
                                todo!()
                            }
                            _ => {
                                return ExprKind::Quote(Box::new(Quote::new(
                                    l.get(2).unwrap().clone(),
                                    SyntaxObject::default(TokenType::Quote),
                                )))
                            }
                        }
                    }

                    // Then this is a contract out, and we should handle it here

                    ExprKind::Quote(Box::new(Quote::new(
                        l.get(2).unwrap().clone(),
                        SyntaxObject::default(TokenType::Quote),
                    )))
                    // ExprKind::Quote(Box::new(Quote::new(
                    //     x,
                    //     SyntaxObject::default(TokenType::Quote),
                    // )))
                } else {
                    panic!("TODO this shouldn't be possible")
                }
            }),
            right,
        ));

        let module_define = ExprKind::Define(Box::new(Define::new(
            ExprKind::atom(CompactString::new(MODULE_PREFIX) + &prefix),
            ExprKind::List(List::new(hash_body)),
            SyntaxObject::default(TokenType::Quote),
        )));
        // } else {
        //     println!("Didn't find any provides: {:?} - {}", self.name, prefix);

        //     let res = ExprKind::List(List::new(hash_body));

        //     res
        // };

        // println!("{}", module_define);

        // let mut offset = None;

        // Find offset of first non builtin require definition:
        // for (idx, expr) in exprs.iter().enumerate() {
        //     if let ExprKind::Define(d) = expr {
        //         // if !is_a_builtin_definition(d) || !is_a_require_definition(d) {
        //         if !is_a_builtin_definition(d) {
        //             // println!("Found offset at: {:?}", offset);

        //             offset = Some(idx);
        //             println!("Found offset at: {:?}", offset);
        //             break;
        //         }
        //     }
        // }

        exprs.push(module_define);

        // exprs.append(&mut provide_definitions);

        let mut builtin_definitions = Vec::new();

        exprs.retain_mut(|expr| {
            if let ExprKind::Define(d) = expr {
                if is_a_builtin_definition(d) {
                    builtin_definitions.push(core::mem::take(expr));
                    false
                } else {
                    true
                }
            } else {
                true
            }
        });

        builtin_definitions.append(&mut provide_definitions);

        let module = self.name.as_os_str().to_str().unwrap().to_owned();

        // Introduce a call to set the current module context?
        builtin_definitions.push(expr_list!(
            ExprKind::atom("#%prim.#%push-module-context"),
            ExprKind::string_lit(module)
        ));

        builtin_definitions.append(&mut exprs);

        builtin_definitions.push(expr_list!(ExprKind::atom("#%prim.#%pop-module-context"),));

        // provide_definitions.append(&mut builtin_definitions);
        // provide_definitions.append(&mut exprs);

        exprs = builtin_definitions;

        // if let Some(offset) = offset {
        // for (idx, expr) in provide_definitions.into_iter().enumerate() {
        //     exprs.insert(offset + idx, expr);
        // }
        // } else {
        // provide_definitions.append(&mut exprs);
        // }

        // println!("MODULE DEFINITIONS----");

        // exprs.pretty_print();

        // println!("END MODULE DEFINITIONS");

        // exprs.pretty_print();

        // exprs.push(module_define);

        // Construct the overall definition
        // TODO: Perhaps mangle these as well, especially if they have contracts associated with them

        // if offset.is_none() {
        //     provide_definitions.append(&mut exprs);
        // }

        let res = ExprKind::Begin(Box::new(Begin::new(
            exprs,
            SyntaxObject::default(TokenType::Begin),
        )));

        // Don't include this... yet
        // self.compiled_ast = Some(res.clone());

        Ok(res)
    }

    // Turn the module into the AST node that represents the macro module in the stdlib
    fn _to_module_ast_node(&self) -> ExprKind {
        let mut body = thin_vec![
            ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Identifier(
                "module".into(),
            )))),
            ExprKind::Atom(Atom::new(SyntaxObject::default(TokenType::Identifier(
                ("___".to_string() + self.name.to_str().unwrap()).into(),
            )))),
        ];

        // Put any provides at the top
        body.extend(self.provides.clone());

        // Include any dependencies here
        // body.append(&mut self.requires.clone());

        // TODO: @Matt 10/8/22
        // Reconsider how to address this expansion.
        // We really don't want to pollute the module space - perhaps disallow shadowed built-ins so we don't need this?
        // That would probably be annoying
        // let steel_base = ExprKind::List(List::new(vec![ExprKind::atom("steel/base".to_string())]));

        // self.ast.pretty_print();

        // body.push(steel_base);

        // Put the ast nodes inside the macro
        body.extend(self.ast.clone());

        // TODO clean this up
        let res = ExprKind::List(List::new(body));

        // if log_enabled!(target: "requires", log::Level::Debug) {
        //     debug!(target: "requires", "Module ast node: {}", res.to_string());
        // }

        res
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum MaybeRenamed {
    Normal(ExprKind),
    Renamed(ExprKind, ExprKind),
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RequireObject {
    pub path: PathOrBuiltIn,
    pub for_syntax: bool,
    pub idents_to_import: Vec<MaybeRenamed>,
    pub prefix: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum PathOrBuiltIn {
    BuiltIn(Cow<'static, str>),
    Path(PathBuf),
}

impl PathOrBuiltIn {
    pub fn get_path(&self) -> Cow<'_, PathBuf> {
        match self {
            Self::Path(p) => Cow::Borrowed(p),
            Self::BuiltIn(p) => Cow::Owned(PathBuf::from(p.to_string())),
        }
    }
}

#[derive(Default, Debug, Clone)]
struct RequireObjectBuilder {
    path: Option<PathOrBuiltIn>,
    for_syntax: bool,
    idents_to_import: Vec<MaybeRenamed>,
    // Built up prefix
    prefix: Option<String>,
    span: Span,
}

impl RequireObjectBuilder {
    fn build(self) -> Result<RequireObject> {
        let path = self
            .path
            .ok_or_else(crate::throw!(Generic => "require must have a path!"))?;

        Ok(RequireObject {
            path,
            for_syntax: self.for_syntax,
            idents_to_import: self.idents_to_import,
            prefix: self.prefix,
            span: self.span,
        })
    }
}

fn try_canonicalize(path: PathBuf) -> PathBuf {
    std::fs::canonicalize(&path).unwrap_or_else(|_| path)
}

/*
#[derive(Default, Clone)]
struct DependencyGraph {
    downstream: HashMap<PathBuf, Vec<PathBuf>>,
}

impl DependencyGraph {
    // Adding edges downward.
    pub fn add_edges(&mut self, parent: PathBuf, children: Vec<PathBuf>) {
        self.downstream.insert(parent, children);
    }

    pub fn remove(&mut self, parent: &PathBuf) {
        self.downstream.remove(parent);
    }

    pub fn add_edge(&mut self, parent: &PathBuf, child: PathBuf) {
        if let Some(children) = self.downstream.get_mut(parent) {
            children.push(child);
        } else {
            self.downstream.insert(parent.clone(), vec![child]);
        }
    }

    // Check everything downstream of this, to see if anything needs to be invalidated
    pub fn check_downstream_changes(
        &self,
        root: &PathBuf,
        updated_at: &crate::HashMap<PathBuf, SystemTime>,
    ) -> std::io::Result<bool> {
        let mut stack = vec![root];

        while let Some(next) = stack.pop() {
            let meta = std::fs::metadata(next)?;

            if let Some(prev) = updated_at.get(next) {
                if *prev != meta.modified()? {
                    return Ok(true);
                }
            }

            if let Some(children) = self.downstream.get(next) {
                for child in children {
                    stack.push(child);
                }
            }
        }

        Ok(false)
    }
}
*/

#[derive(Clone)]
#[allow(unused)]
pub(crate) struct CompiledModuleCache {
    cache_dir: Option<Arc<PathBuf>>,
    compiled_modules: crate::HashMap<PathBuf, CompiledModule>,
}

// impl Drop for ModuleManager {
// fn drop(&mut self) {
// self.compiled_modules.cache_modules();
// }
// }

#[allow(unused)]
impl CompiledModuleCache {
    fn cache_module(&mut self, key: &PathBuf, module: &CompiledModule) {
        if let Some(cache_dir) = &self.cache_dir {
            let key = Self::create_key(&cache_dir, key);

            if key.exists() {
                return;
            }

            let encoded = bincode::serialize(&module).unwrap();
            log::info!("Writing to key: {:?}", key);
            let parent = key.parent().unwrap();
            if !parent.exists() {
                std::fs::create_dir_all(parent).unwrap();
            }
            if !key.exists() {
                std::fs::write(key, encoded).unwrap();
            }
        }
    }

    pub fn create_key(cache_dir: &PathBuf, key: &PathBuf) -> PathBuf {
        if key.exists() {
            let parts: PathBuf = key.components().skip(1).collect();
            cache_dir.join(parts)
        } else {
            cache_dir.join(key)
        }
    }

    pub fn get_cached(&mut self, path: &PathBuf, sources: &mut Sources) -> Option<&CompiledModule> {
        self.read_cached_module(path, sources)?;
        self.compiled_modules.get(path)
    }

    pub fn get_cached_mut(
        &mut self,
        path: &PathBuf,
        sources: &mut Sources,
    ) -> Option<&mut CompiledModule> {
        self.read_cached_module(path, sources)?;
        self.compiled_modules.get_mut(path)
    }

    // Note: Some modules simply cannot be cached.
    // If there are modules where we need the side effects of compilation, i.e.
    // anything to do with the kernel, we should designate that some side
    // effect too place and make sure to not include those in the cache.
    fn read_cached_module(&mut self, path: &PathBuf, sources: &mut Sources) -> Option<()> {
        // Load the module in the background from the cache
        static BACKGROUND_DESERIALIZING: Lazy<(
            Mutex<HashMap<PathBuf, Option<CompiledModule>>>,
            Sender<PathBuf>,
        )> = Lazy::new(|| {
            let (sender, receiver) = crossbeam_channel::unbounded();

            std::thread::spawn(move || {
                for key in receiver {
                    log::info!("Background thread received: {:?}", key);
                    let guard = BACKGROUND_DESERIALIZING.0.lock();
                    if !guard.contains_key(&key) {
                        drop(guard);
                        if let Ok(contents) = std::fs::read(&key) {
                            let value: bincode::Result<CompiledModule> =
                                bincode::deserialize(&contents);
                            match value {
                                Ok(mut value) => {
                                    value.emitted = false;
                                    value.cached_prefix =
                                        path_to_prefix_name(value.name.to_path_buf()).into();

                                    log::info!(
                                        "Successfully read cached module in background -> {:?}",
                                        key
                                    );

                                    BACKGROUND_DESERIALIZING.0.lock().insert(key, Some(value));
                                }
                                Err(e) => {
                                    log::info!("Error: {:?}", e);
                                }
                            }
                        }
                    }
                }

                log::info!("Thread finished");
            });

            (Mutex::new(HashMap::new()), sender)
        });

        fn drain_module(key: &PathBuf) -> Option<CompiledModule> {
            BACKGROUND_DESERIALIZING
                .0
                .lock()
                .get_mut(key)
                .and_then(|x| x.take())
        }

        fn enqueue_module(key: PathBuf) {
            BACKGROUND_DESERIALIZING.1.send(key).unwrap();
        }

        let now = crate::time::Instant::now();

        if let Some(cache_dir) = &self.cache_dir {
            let key = Self::create_key(cache_dir, path);

            if let Some(value) = drain_module(&key) {
                self.compiled_modules.insert(path.to_owned(), value);
                return Some(());
            }

            // Check the cache first, otherwise
            // kick off loading the background values:

            let contents = std::fs::read(&key).ok()?;
            let mut value: CompiledModule = bincode::deserialize(&contents).unwrap();

            value.emitted = false;
            value.cached_prefix = path_to_prefix_name(value.name.to_path_buf()).into();

            for downstream in value
                .downstream
                .iter()
                .chain(value.downstream_builtins.iter())
            {
                enqueue_module(Self::create_key(&cache_dir, downstream));
            }

            log::info!("Downstream: {:?}", value.downstream);
            log::info!("Downstream builtins: {:?}", value.downstream_builtins);

            self.compiled_modules.insert(path.to_owned(), value);

            log::info!(
                "Successfully read cached module: {:?} - {:?}",
                path,
                now.elapsed()
            );

            Some(())
        } else {
            None
        }
    }

    #[cfg(not(target_family = "wasm"))]
    pub fn new(compiled_modules: crate::HashMap<PathBuf, CompiledModule>) -> Self {
        let home = PathBuf::from(steel_home().unwrap());

        let cache_dir = Arc::new(home.join("cached-modules"));

        if !cache_dir.exists() {
            std::fs::create_dir(cache_dir.as_path()).ok();
        }

        Self {
            cache_dir: Some(cache_dir),
            compiled_modules,
        }
    }

    #[cfg(target_family = "wasm")]
    pub fn new(compiled_modules: crate::HashMap<PathBuf, CompiledModule>) -> Self {
        Self {
            cache_dir: None,
            compiled_modules,
        }
    }

    pub fn get(&mut self, key: &PathBuf, sources: &mut Sources) -> Option<&CompiledModule> {
        // if !self.compiled_modules.contains_key(key) {
        //     return self.get_cached(key, sources);
        // }

        self.compiled_modules.get(key)
    }

    pub fn cached_mut(
        &mut self,
        key: &PathBuf,
        sources: &mut Sources,
    ) -> Option<&mut CompiledModule> {
        if !self.compiled_modules.contains_key(key) {
            return self.get_cached_mut(key, sources);
        }

        self.compiled_modules.get_mut(key)
    }
}

// impl core::ops::Deref for CompiledModuleCache {
//     type Target = crate::HashMap<PathBuf, CompiledModule>;

//     fn deref(&self) -> &Self::Target {
//         &self.compiled_modules
//     }
// }

// impl core::ops::DerefMut for CompiledModuleCache {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.compiled_modules
//     }
// }

struct ModuleBuilder<'a> {
    name: PathBuf,
    main: bool,
    source_ast: Vec<ExprKind>,
    local_macros: FxHashSet<InternedString>,
    macro_map: Arc<FxHashMap<InternedString, SteelMacro>>,
    // TODO: Change the requires / requires_for_syntax to just be a require enum?
    require_objects: Vec<RequireObject>,

    provides: Vec<ExprKind>,
    provides_for_syntax: Vec<ExprKind>,
    compiled_modules: &'a mut CompiledModuleCache,
    visited: &'a mut FxHashSet<PathBuf>,
    file_metadata: &'a mut crate::HashMap<PathBuf, SystemTime>,
    sources: &'a mut Sources,
    kernel: &'a mut Option<Kernel>,
    builtin_modules: ModuleContainer,
    global_macro_map: &'a FxHashMap<InternedString, SteelMacro>,
    global_bindings: GlobalMap<'a>,
    custom_builtins: &'a HashMap<String, String>,
    search_dirs: &'a [PathBuf],
    module_resolvers: &'a [Arc<dyn SourceModuleResolver>],
    prelude_string: &'a str,
    parsed_requires: FxHashMap<PathBuf, ParsedModule>,
}

struct ParsedModule {
    ast: Vec<ExprKind>,
    metadata: Option<SystemTime>,
    requires: FxHashMap<PathBuf, ParsedModule>,
}

#[derive(Clone)]
struct ModuleExports {
    provides: Vec<ExprKind>,
    provides_for_syntax: Vec<InternedString>,
    macros: Arc<FxHashMap<InternedString, SteelMacro>>,
    runtime_bindings: FxHashSet<InternedString>,
}

#[derive(Debug)]
pub struct RequiredModuleMacros {
    pub module_key: PathBuf,
    pub module_name: String,
    pub module_macros: Arc<FxHashMap<InternedString, SteelMacro>>,
    pub in_scope_macros: FxHashMap<InternedString, SteelMacro>,
    pub name_mangler: NameMangler,
}

fn retain_imported_macros<'a>(
    macros: &mut Arc<FxHashMap<InternedString, SteelMacro>>,
    required: &[RequiredModuleMacros],
    shadowed: &FxHashSet<InternedString>,
    module: &PathBuf,
    provided: impl Iterator<Item = &'a InternedString>,
) {
    if required.is_empty() {
        return;
    }
    // The module's own definitions, runtime or syntax, shadow an import of the same name.
    let imported = |name: &InternedString| !shadowed.contains(name) && !macros.contains_key(name);
    let mut imports = FxHashMap::default();
    let mut dependencies = FxHashMap::default();
    for required in required {
        if !required.in_scope_macros.keys().any(imported) {
            continue;
        }
        let prefix = CompactString::new(MACRO_MANGLE_PREFIX)
            + &path_to_prefix_name(required.module_key.clone());
        let mut mangler = NameMangler::new(
            required
                .module_macros
                .keys()
                .filter(|name| !name.resolve().starts_with(MACRO_MANGLE_PREFIX))
                .copied()
                .collect(),
            prefix.clone(),
        );
        let mut qualify = |smacro: &SteelMacro| {
            let mut smacro = smacro.clone();
            if !smacro.special_mangled {
                mangler.mangle_macro(&mut smacro);
                smacro.special_mangled = true;
            }
            smacro
        };
        // Keep the provider's private dependencies under names only its templates reference.
        for (name, smacro) in required.module_macros.iter() {
            let name = if name.resolve().starts_with(MACRO_MANGLE_PREFIX) {
                *name
            } else {
                (prefix.clone() + name.resolve()).into()
            };
            dependencies.insert(name, qualify(smacro));
        }
        for (name, smacro) in &required.in_scope_macros {
            if imported(name) {
                imports.entry(*name).or_insert_with(|| qualify(smacro));
            }
        }
    }
    if imports.is_empty() {
        return;
    }
    let prefix = CompactString::new(MACRO_MANGLE_PREFIX) + &path_to_prefix_name(module.clone());
    let mut mangler = NameMangler::new(imports.keys().copied().collect(), prefix.clone());
    let macros = Arc::make_mut(macros);
    for smacro in macros.values_mut() {
        mangler.mangle_macro(smacro);
    }
    for name in provided {
        if let Some(smacro) = imports.get(name) {
            macros.insert(*name, smacro.clone());
        }
    }
    macros.extend(
        imports
            .into_iter()
            .map(|(name, smacro)| ((prefix.clone() + name.resolve()).into(), smacro)),
    );
    macros.extend(dependencies);
}

fn imported_bindings(
    require: &RequireObject,
    provides: &[ExprKind],
    provides_for_syntax: &[InternedString],
    macros: &FxHashMap<InternedString, SteelMacro>,
    mut define: impl FnMut(InternedString, Option<&SteelMacro>),
) {
    let provided = provides
        .iter()
        .flat_map(|expr| &expr.list().unwrap().args[1..])
        .filter_map(|provide| match provide {
            ExprKind::Atom(_) => provide.atom_identifier(),
            ExprKind::List(list)
                if list.first_ident() == Some(&*REQUIRE_IDENT_SPEC)
                    && !macros.contains_key(&*REQUIRE_IDENT_SPEC) =>
            {
                list.second_ident()
            }
            _ => None,
        })
        .chain(
            provides_for_syntax
                .iter()
                .filter(|name| macros.contains_key(name)),
        );
    let mut import = |from: &InternedString, to: &InternedString| {
        let imported = match &require.prefix {
            Some(prefix) => (prefix.clone() + to.resolve()).into(),
            None => *to,
        };
        define(imported, macros.get(from));
    };
    if require.idents_to_import.is_empty() {
        for name in provided {
            import(name, name);
        }
    } else {
        let provided = provided.collect::<FxHashSet<_>>();
        // Match compilation's import order: keep every alias, with later destinations winning.
        for ident in &require.idents_to_import {
            let (from, to) = match ident {
                MaybeRenamed::Normal(name) => (name, name),
                MaybeRenamed::Renamed(from, to) => (from, to),
            };
            let from = from.atom_identifier().unwrap();
            if provided.contains(from) {
                import(from, to.atom_identifier().unwrap());
            }
        }
    }
}

fn collect_main_literal_bindings(
    ast: &[ExprKind],
    global_map: &FxHashMap<InternedString, usize>,
    pending_globals: &FxHashSet<InternedString>,
    is_macro: &dyn Fn(&InternedString) -> bool,
    builtin_modules: &ModuleContainer,
) -> FxHashSet<InternedString> {
    let mut bindings = FxHashSet::default();
    predeclare_native_definitions(
        ast,
        &|name| pending_globals.contains(name),
        GlobalMap::Map(global_map),
        is_macro,
        Some(builtin_modules),
        &mut |name| {
            bindings.insert(name);
        },
    );
    bindings
}

#[cfg(test)]
thread_local! {
    static MAIN_LITERAL_REFRESH_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn refresh_main_literals(
    ast: &[ExprKind],
    macros: &mut FxHashMap<InternedString, SteelMacro>,
    program_macros: &FxHashSet<InternedString>,
    global_map: &FxHashMap<InternedString, usize>,
    pending_globals: &FxHashSet<InternedString>,
    deferred_macros: &FxHashSet<InternedString>,
    builtin_modules: &ModuleContainer,
) -> FxHashSet<InternedString> {
    #[cfg(test)]
    MAIN_LITERAL_REFRESH_COUNT.with(|count| count.set(count.get() + 1));

    // Rebuild speculative bindings: an earlier expansion can turn a native form into a call.
    let mut literal_globals = collect_main_literal_bindings(
        ast,
        global_map,
        pending_globals,
        &|name| macros.contains_key(name) || deferred_macros.contains(name),
        builtin_modules,
    );
    literal_globals.extend(pending_globals.iter().copied());
    bind_program_literals(macros, program_macros, global_map, &literal_globals);
    literal_globals
}

fn bind_program_literals(
    macros: &mut FxHashMap<InternedString, SteelMacro>,
    program_macros: &FxHashSet<InternedString>,
    global_map: &FxHashMap<InternedString, usize>,
    literal_globals: &FxHashSet<InternedString>,
) {
    for name in program_macros {
        if let Some(smacro) = macros.get_mut(name) {
            smacro.bind_global_literals(GlobalMap::Layered(global_map, literal_globals));
        }
    }
}

// Pending globals reach native bindings only through the native heads they can shadow.
fn shadows_native_head(name: InternedString) -> bool {
    name == *STRUCT_KEYWORD || name == *DEFINE_VALUES || is_marked_native_head(name)
}

fn shadows_any_native_head(literal_globals: &FxHashSet<InternedString>) -> bool {
    literal_globals
        .iter()
        .any(|name| shadows_native_head(*name))
}

// Merge a statement's expansion into the literal bindings. Return whether they must instead be
// rebuilt from the whole program, and whether they changed. Plain definitions bind the same names
// in any context, so only names that can shadow native heads need a rebuild. A native form's
// bindings depend on the earlier bindings of its head, which this statement alone sees only when
// `native_heads_shadowed` says that no known binding shadows a native head.
fn update_main_literals(
    statement: &ExprKind,
    previous_bindings: &FxHashSet<InternedString>,
    bindings: &FxHashSet<InternedString>,
    native_heads_shadowed: bool,
    pending_globals: &mut FxHashSet<InternedString>,
    literal_globals: &mut FxHashSet<InternedString>,
) -> (bool, bool) {
    let mut definitions = FxHashSet::default();
    collect_define_syntax(std::slice::from_ref(statement), &mut |name, syntax| {
        definitions.insert(native_binding_name(name, syntax));
    });
    let mut refresh = previous_bindings
        .iter()
        .any(|name| !bindings.contains(name));
    let mut changed = false;
    for name in bindings.difference(previous_bindings) {
        refresh |=
            native_heads_shadowed && !definitions.contains(name) || shadows_native_head(*name);
        changed |= literal_globals.insert(*name);
    }
    collect_defines(std::slice::from_ref(statement), &mut |name| {
        if pending_globals.insert(name) {
            refresh |= shadows_native_head(name);
            changed |= literal_globals.insert(name);
        }
    });
    (refresh, changed)
}

#[test]
fn raw_engine_binding_free_expansions_do_not_refresh_main_literals() {
    use crate::{steel_vm::engine::Engine, SteelVal};

    // With an import the early loop expands `m`; otherwise the final loop does.
    for require in ["", "(require \"unused-module\")"] {
        let refresh_counts = [1, 32].map(|calls| {
            let mut engine = Engine::new_raw_no_kernel();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            MAIN_LITERAL_REFRESH_COUNT.with(|count| count.set(0));
            assert_eq!(
                engine
                    .run(format!(
                        "{require} (define-syntax m (syntax-rules () [(m) 42])) {}",
                        "(m)\n".repeat(calls)
                    ))
                    .unwrap()
                    .last(),
                Some(&SteelVal::IntV(42))
            );
            MAIN_LITERAL_REFRESH_COUNT.with(|count| count.get())
        });
        assert_eq!(refresh_counts[0], refresh_counts[1], "{require}");
    }
}

#[test]
fn raw_engine_native_definitions_do_not_refresh_main_literals() {
    use crate::{steel_vm::engine::Engine, SteelVal};

    // A native form, written out or generated, binds the same names in any context unless a
    // binding shadows its head. Each lowering also names its private temporary afresh, which is
    // not a changed binding.
    let macros = "(define-syntax make-struct (syntax-rules () [(_ name) (struct name (x))]))
                  (define-syntax make-values
                    (syntax-rules () [(_ name) (define-values (name) '(42))]))";
    for require in ["", "(require \"unused-module\")"] {
        for (definition, read) in [
            ("(struct point{} (x))", "(point0-x (point0 42))"),
            ("(define-values (value{}) '(42))", "value0"),
            ("(make-struct point{})", "(point0-x (point0 42))"),
            ("(make-values value{})", "value0"),
        ] {
            let refresh_counts = [1, 32].map(|count| {
                let mut engine = Engine::new_raw_no_kernel();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                let definitions = (0..count)
                    .map(|index| definition.replace("{}", &index.to_string()))
                    .collect::<Vec<_>>()
                    .join("\n");
                MAIN_LITERAL_REFRESH_COUNT.with(|count| count.set(0));
                assert_eq!(
                    engine
                        .run(format!("{require} {macros} {definitions} {read}"))
                        .unwrap()
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {definition}"
                );
                MAIN_LITERAL_REFRESH_COUNT.with(|count| count.get())
            });
            assert_eq!(
                refresh_counts[0], refresh_counts[1],
                "{require}, {definition}"
            );
        }
    }
}

#[test]
fn raw_engine_generated_definitions_do_not_refresh_main_literals() {
    use crate::{steel_vm::engine::Engine, SteelVal};

    // A generated definition that cannot shadow a native head joins the literals incrementally.
    for require in ["", "(require \"unused-module\")"] {
        let refresh_counts = [1, 32].map(|calls| {
            let mut engine = Engine::new_raw_no_kernel();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            let definitions = (0..calls)
                .map(|index| format!("(make value{index})\n"))
                .collect::<String>();
            MAIN_LITERAL_REFRESH_COUNT.with(|count| count.set(0));
            assert_eq!(
                engine
                    .run(format!(
                        "{require}
                         (define-syntax make (syntax-rules () [(make name) (define name 42)]))
                         (define-syntax classify
                           (syntax-rules (value0) [(classify value0) 1] [(classify other) 2]))
                         {definitions} (classify value0)"
                    ))
                    .unwrap()
                    .last(),
                Some(&SteelVal::IntV(1))
            );
            MAIN_LITERAL_REFRESH_COUNT.with(|count| count.get())
        });
        assert_eq!(refresh_counts[0], refresh_counts[1], "{require}");
    }
}

// Bodies can expand before a native definition after a macro call is prepared, so predeclare the
// bindings of every native definition for bodies. Heads check `native_heads` instead, so a form
// binding a native form's name itself still lowers natively.
fn predeclare_native_bindings(
    ast: &[ExprKind],
    global_bindings: GlobalMap,
    native_heads: &FxHashSet<InternedString>,
    native_globals: &mut FxHashSet<InternedString>,
    is_macro: &dyn Fn(&InternedString) -> bool,
    builtin_modules: &ModuleContainer,
) {
    predeclare_native_definitions(
        ast,
        &|name| native_heads.contains(name),
        // Module heads see only the module's bindings, and global template heads see
        // `global_bindings`.
        GlobalMap::Scoped(&global_bindings, &FxHashSet::default()),
        is_macro,
        Some(builtin_modules),
        &mut |name| {
            native_globals.insert(name);
        },
    );
}

// Prepare native heads from `ast[index]` up to the next macro call, recording their definitions
// for both heads and bodies. Return the index to prepare from next.
fn prepare_native_heads(
    ast: &mut [ExprKind],
    index: usize,
    global_bindings: GlobalMap,
    native_heads: &mut FxHashSet<InternedString>,
    native_globals: &mut FxHashSet<InternedString>,
    is_macro: &dyn Fn(&InternedString) -> bool,
) -> Result<usize> {
    let count = prepare_native_globals(
        &mut ast[index..],
        GlobalMap::Scoped(&global_bindings, native_heads),
        is_macro,
    )?;
    collect_defines(&ast[index..index + count], &mut |name| {
        native_heads.insert(name);
        native_globals.insert(name);
    });
    Ok(index + count)
}

// A flattened top-level begin: its emptied wrapper and the shapes of its children.
enum BeginShape {
    Leaf,
    Group(ExprKind, Vec<BeginShape>),
}

// The deferred pass must process nested top-level begins in statement order too.
fn flatten_module_begins(ast: &mut Vec<ExprKind>) -> Result<()> {
    flatten_main_begins(ast).map(drop)
}

// Main regroups afterwards with regroup_main_begins, since each statement returns one result.
fn flatten_main_begins(ast: &mut Vec<ExprKind>) -> Result<Vec<BeginShape>> {
    fn flatten(expr: ExprKind, leaves: &mut Vec<ExprKind>) -> Result<BeginShape> {
        let (wrapper, children) = match expr {
            ExprKind::Begin(mut begin) if !begin.exprs.is_empty() => {
                let children = core::mem::take(&mut begin.exprs);
                (ExprKind::Begin(begin), children)
            }
            ExprKind::List(mut list)
                if list.len() > 1 && list.first().is_some_and(is_begin_head) =>
            {
                if list.improper {
                    stop!(BadSyntax => "begin expression requires a proper list"; list.location);
                }
                let children = list.args.split_off(1).into_iter().collect();
                (ExprKind::List(list), children)
            }
            expr => {
                leaves.push(expr);
                return Ok(BeginShape::Leaf);
            }
        };
        let children = children
            .into_iter()
            .map(|child| flatten(child, leaves))
            .collect::<Result<_>>()?;
        Ok(BeginShape::Group(wrapper, children))
    }

    let exprs = core::mem::take(ast);
    exprs.into_iter().map(|expr| flatten(expr, ast)).collect()
}

fn regroup_main_begins(ast: &mut Vec<ExprKind>, shapes: Vec<BeginShape>) {
    fn regroup(shape: BeginShape, leaves: &mut std::vec::IntoIter<ExprKind>) -> ExprKind {
        match shape {
            BeginShape::Leaf => leaves.next().expect("flattened statement count changed"),
            BeginShape::Group(mut wrapper, children) => {
                let children = children.into_iter().map(|child| regroup(child, leaves));
                match &mut wrapper {
                    ExprKind::Begin(begin) => begin.exprs.extend(children),
                    ExprKind::List(list) => list.args.extend(children),
                    _ => unreachable!("begin wrappers are begins or lists"),
                }
                wrapper
            }
        }
    }

    let mut leaves = core::mem::take(ast).into_iter();
    *ast = shapes
        .into_iter()
        .map(|shape| regroup(shape, &mut leaves))
        .collect();
    debug_assert!(leaves.next().is_none(), "flattened statement count changed");
}

impl<'a> ModuleBuilder<'a> {
    #[allow(clippy::too_many_arguments)]
    #[allow(unused)]
    fn main(
        name: Option<PathBuf>,
        source_ast: Vec<ExprKind>,
        compiled_modules: &'a mut CompiledModuleCache,
        visited: &'a mut FxHashSet<PathBuf>,
        file_metadata: &'a mut crate::HashMap<PathBuf, SystemTime>,
        sources: &'a mut Sources,
        kernel: &'a mut Option<Kernel>,
        builtin_modules: ModuleContainer,
        global_macro_map: &'a FxHashMap<InternedString, SteelMacro>,
        global_bindings: GlobalMap<'a>,
        custom_builtins: &'a HashMap<String, String>,
        search_dirs: &'a [PathBuf],
        module_resolvers: &'a [Arc<dyn SourceModuleResolver>],
        prelude_string: &'a str,
    ) -> Result<Self> {
        // TODO don't immediately canonicalize the path unless we _know_ its coming from a path
        // change the path to not always be required
        // if its not required we know its not coming in

        #[cfg(not(target_family = "wasm"))]
        let name = if let Some(p) = name {
            std::fs::canonicalize(p)?
        } else {
            std::env::current_dir()?
        };

        #[cfg(target_family = "wasm")]
        let name = PathBuf::new();

        Ok(ModuleBuilder {
            name,
            main: true,
            source_ast,
            local_macros: FxHashSet::default(),
            macro_map: default_prelude_macros(),
            require_objects: Vec::new(),
            provides: Vec::new(),
            provides_for_syntax: Vec::new(),
            compiled_modules,
            visited,
            file_metadata,
            sources,
            kernel,
            builtin_modules,
            global_macro_map,
            global_bindings,
            custom_builtins,
            search_dirs,
            module_resolvers,
            prelude_string,
            parsed_requires: FxHashMap::default(),
        })
    }

    // Discover main's imported values and macros before compiling any module bodies.
    fn predeclare_imports(
        &mut self,
        globals: &mut FxHashSet<InternedString>,
        imports: &mut HashSet<InternedString>,
        macros: &mut FxHashSet<InternedString>,
    ) -> Result<()> {
        let mut record = |name, smacro: Option<&SteelMacro>| {
            imports.insert(name);
            if smacro.is_some() {
                macros.insert(name);
            } else {
                globals.insert(name);
            }
        };
        let mut discovered = FxHashMap::default();
        for require in self.require_objects.clone() {
            // Point a module that fails to load at the require, as compilation would.
            let exports = self
                .discover_exports(&require.path, &mut discovered)
                .map_err(|err| err.set_span_if_none(require.span))?;
            imported_bindings(
                &require,
                &exports.provides,
                &exports.provides_for_syntax,
                &exports.macros,
                &mut record,
            );
        }
        Ok(())
    }

    fn cached_exports_are_current(&self, path: &PathOrBuiltIn) -> bool {
        let mut pending = vec![path.clone()];
        let mut checked = FxHashSet::default();
        while let Some(path) = pending.pop() {
            let name = path.get_path();
            if !checked.insert(name.clone().into_owned()) {
                continue;
            }
            if matches!(path, PathOrBuiltIn::Path(_))
                && !std::fs::metadata(name.as_ref())
                    .and_then(|metadata| metadata.modified())
                    .is_ok_and(|modified| self.file_metadata.get(name.as_ref()) == Some(&modified))
            {
                return false;
            }
            let Some(module) = self.compiled_modules.compiled_modules.get(name.as_ref()) else {
                return false;
            };
            pending.extend(
                module
                    .require_objects
                    .iter()
                    .map(|require| require.path.clone()),
            );
        }
        true
    }

    fn discover_exports(
        &mut self,
        required: &PathOrBuiltIn,
        discovered: &mut FxHashMap<PathBuf, ModuleExports>,
    ) -> Result<ModuleExports> {
        let path = required.get_path().into_owned();
        if let Some(exports) = discovered.get(&path) {
            return Ok(exports.clone());
        }
        if self.cached_exports_are_current(required) {
            let module = &self.compiled_modules.compiled_modules[&path];
            let mut runtime_bindings = collect_globals(&module.ast);
            for require in &module.require_objects {
                let imported =
                    &self.compiled_modules.compiled_modules[require.path.get_path().as_ref()];
                imported_bindings(
                    require,
                    &imported.provides,
                    &imported.provides_for_syntax,
                    &imported.macro_map,
                    |name, smacro| {
                        if smacro.is_none() {
                            runtime_bindings.insert(name);
                        }
                    },
                );
            }
            let exports = ModuleExports {
                provides: module.provides.clone(),
                provides_for_syntax: module.provides_for_syntax.clone(),
                macros: module.macro_map.clone(),
                runtime_bindings,
            };
            discovered.insert(path, exports.clone());
            return Ok(exports);
        }
        if !self.visited.insert(path.clone()) {
            stop!(Generic => format!("circular dependency found during module resolution with: {:?}", path));
        }
        let previous_metadata = self.file_metadata.get(&path).copied();
        let result = self.load_required(required).and_then(|mut module| {
            let mut parsed = ParsedModule {
                ast: module.source_ast.clone(),
                metadata: module.file_metadata.get(&path).copied(),
                requires: FxHashMap::default(),
            };
            module.collect_requires()?;
            module.collect_provides()?;
            module.extract_macro_defs()?;
            let mut module_globals = collect_globals(&module.source_ast);
            let mut required_macros = Vec::new();
            let mut shadowed = FxHashSet::default();
            for require in module.require_objects.clone() {
                let mut exports = module
                    .discover_exports(&require.path, discovered)
                    .map_err(|err| err.set_span_if_none(require.span))?;
                let mut name_mangler = NameMangler::new(
                    exports.runtime_bindings,
                    path_to_prefix_name(require.path.get_path().into_owned()).into(),
                );
                // Imported templates retain their provider's private runtime bindings.
                for smacro in Arc::make_mut(&mut exports.macros).values_mut() {
                    if !smacro.special_mangled && !smacro.is_mangled() {
                        name_mangler.mangle_macro(smacro);
                        smacro.mark_mangled();
                    }
                }
                let mut imported_macros = FxHashMap::default();
                imported_bindings(
                    &require,
                    &exports.provides,
                    &exports.provides_for_syntax,
                    &exports.macros,
                    |name, smacro| {
                        if let Some(smacro) = smacro {
                            imported_macros.insert(name, smacro.clone());
                        } else {
                            shadowed.insert(name);
                        }
                    },
                );
                required_macros.push(RequiredModuleMacros {
                    module_key: require.path.get_path().into_owned(),
                    module_name: require.path.get_path().to_str().unwrap().to_owned(),
                    module_macros: exports.macros,
                    in_scope_macros: imported_macros,
                    name_mangler,
                });
            }
            module_globals.extend(shadowed.iter().copied());
            predeclare_native_bindings(
                &module.source_ast,
                module.global_bindings,
                &shadowed,
                &mut module_globals,
                &|name| {
                    module.macro_map.contains_key(name)
                        || module.global_macro_map.contains_key(name)
                        || required_macros
                            .iter()
                            .any(|required| required.in_scope_macros.contains_key(name))
                },
                &module.builtin_modules,
            );
            let globals = GlobalMap::Set(&module_globals);
            let overlays = required_macros
                .iter_mut()
                .map(|map| RequiredMacroMap {
                    map,
                    changed: false,
                })
                .collect();
            // Provides use the transformers available before runtime definitions shadow them.
            let provide_macros = module.macro_map.clone();
            let mut expander =
                ExpanderMany::new(Arc::make_mut(&mut module.macro_map), overlays, globals);
            expander.global_macro_map = Some(module.global_macro_map);
            let imported_bindings = shadowed.clone();
            let mut definitions = FxHashSet::default();
            // Top-level macros can produce exports; ordinary bodies need not expand yet.
            for expr in &mut module.source_ast {
                expander.expand_top_level(expr, &mut shadowed)?;
                predeclare_native_bindings(
                    std::slice::from_ref(expr),
                    module.global_bindings,
                    &shadowed,
                    &mut definitions,
                    &|name| {
                        module.global_macro_map.contains_key(name)
                            || expander.map.contains_key(name)
                            || expander
                                .overlays
                                .iter()
                                .any(|overlay| overlay.map.in_scope_macros.contains_key(name))
                    },
                    &module.builtin_modules,
                );
                collect_defines(std::slice::from_ref(expr), &mut |name| {
                    definitions.insert(name);
                });
                shadowed.extend(definitions.drain());
            }
            flatten_module_begins(&mut module.source_ast)?;
            expander.reset_for_replay(&provide_macros, &imported_bindings);
            let mut shadowed = imported_bindings;
            let mut global_shadows = collect_globals(&module.source_ast);
            global_shadows.extend(shadowed.iter().copied());
            let is_macro = |name: &InternedString| module.global_macro_map.contains_key(name);
            // Match compilation: global macro literals see later native and module definitions.
            predeclare_native_bindings(
                &module.source_ast,
                module.global_bindings,
                &shadowed,
                &mut global_shadows,
                &is_macro,
                &module.builtin_modules,
            );
            let mut prepared = 0;
            for index in 0..module.source_ast.len() {
                if index >= prepared {
                    prepared = prepare_native_heads(
                        &mut module.source_ast,
                        index,
                        module.global_bindings,
                        &mut shadowed,
                        &mut global_shadows,
                        &is_macro,
                    )?;
                }
                let expr = &mut module.source_ast[index];
                expander.expand_in_scope(expr)?;
                for overlay in &mut expander.overlays {
                    if overlay.changed {
                        expand_module_scoped(expr, &overlay.map.module_macros, globals)?;
                        overlay.changed = false;
                    }
                }
                let mut expanded = expr.clone();
                // Main can still generate bindings that shadow these macros; compilation validates them.
                if Expander::expand_global_macros(
                    &mut expanded,
                    module.global_macro_map,
                    module.global_bindings,
                    &mut global_shadows,
                    &module.builtin_modules,
                    true,
                )
                .is_ok()
                {
                    *expr = expanded;
                }
                if index >= prepared {
                    prepared = prepare_native_heads(
                        &mut module.source_ast,
                        index,
                        module.global_bindings,
                        &mut shadowed,
                        &mut global_shadows,
                        &is_macro,
                    )?;
                }
                collect_defines(
                    std::slice::from_ref(&module.source_ast[index]),
                    &mut |name| {
                        shadowed.insert(name);
                        global_shadows.insert(name);
                        expander.in_scope_values.define(name);
                        expander.map.remove(&name);
                    },
                );
            }
            flatten_module_begins(&mut module.source_ast)?;
            module.collect_provides()?;
            for provide in &mut module.provides {
                expand(provide, &provide_macros, globals)?;
            }
            for required in &required_macros {
                for provide in &mut module.provides {
                    let exclusions = HashSet::new();
                    let mut expander =
                        Expander::new(&required.in_scope_macros, &exclusions, globals);
                    expander.expand(provide)?;
                    if expander.changed {
                        expand(provide, &required.module_macros, globals)?;
                    }
                }
            }
            retain_imported_macros(
                &mut module.macro_map,
                &required_macros,
                &global_shadows,
                &module.name,
                module
                    .provides_for_syntax
                    .iter()
                    .filter_map(ExprKind::atom_identifier)
                    .chain(module.provides.iter().flat_map(|provide| {
                        provide.list().unwrap().args[1..]
                            .iter()
                            .filter_map(ExprKind::atom_identifier)
                    })),
            );
            parsed.requires = module.parsed_requires;
            Ok((
                parsed,
                ModuleExports {
                    provides: module.provides,
                    provides_for_syntax: module
                        .provides_for_syntax
                        .iter()
                        .filter_map(ExprKind::atom_identifier)
                        .copied()
                        .collect(),
                    macros: module.macro_map,
                    runtime_bindings: global_shadows,
                },
            ))
        });
        // Discovery must not make compilation mistake a changed module for a cached one.
        match previous_metadata {
            Some(previous) => {
                self.file_metadata.insert(path.clone(), previous);
            }
            None => {
                self.file_metadata.remove(&path);
            }
        }
        self.visited.remove(&path);
        let (parsed, exports) = result?;
        self.parsed_requires.insert(path.clone(), parsed);
        discovered.insert(path, exports.clone());
        Ok(exports)
    }

    fn load_required(&mut self, path: &PathOrBuiltIn) -> Result<ModuleBuilder<'_>> {
        let name = path.get_path().into_owned();
        let parsed = self.parsed_requires.remove(&name);
        let mut module = ModuleBuilder::raw(
            name.clone(),
            self.compiled_modules,
            self.visited,
            self.file_metadata,
            self.sources,
            self.kernel,
            self.builtin_modules.clone(),
            self.global_macro_map,
            self.global_bindings,
            self.custom_builtins,
            if matches!(path, PathOrBuiltIn::Path(_)) {
                self.search_dirs
            } else {
                &[]
            },
            self.module_resolvers,
            matches!(path, PathOrBuiltIn::Path(_)),
            self.prelude_string,
        );
        if let Some(parsed) = parsed {
            module.source_ast = parsed.ast;
            module.parsed_requires = parsed.requires;
            if let Some(metadata) = parsed.metadata {
                module.file_metadata.insert(name, metadata);
            }
            return Ok(module);
        }
        if matches!(path, PathOrBuiltIn::Path(_)) {
            return module.parse_from_path();
        }
        let module_name = name;
        let input = BUILT_INS
            .iter()
            .find(|x| x.0 == module_name.to_str().unwrap())
            .map(|x| Cow::Borrowed(x.1))
            .or_else(|| {
                module
                    .custom_builtins
                    .get(module_name.to_str().unwrap())
                    .map(|x| Cow::Owned(x.to_string()))
            })
            .or_else(|| {
                module
                    .module_resolvers
                    .iter()
                    .find_map(|x| x.resolve(module_name.to_str().unwrap()))
                    // Insert the prelude
                    .map(|mut x| {
                        x.insert_str(0, module.prelude_string);
                        x
                    })
                    .map(Cow::Owned)
            })
            .ok_or_else(
                crate::throw!(Generic => "Unable to find builtin module: {:?}", module_name),
            )?;

        module.parse_builtin(input)
    }

    fn compile(&mut self) -> Result<Vec<ExprKind>> {
        // println!("Compiling: {:?}", self.name);

        // debug!(target: "requires", "Visiting: {:?}", self.name);

        // @Matt - 10/3/23
        // This has a relatively fatal flaw at the moment:
        /*

            (define-syntax register-plugin
              (syntax-rules ()
                [(register-plugin plugin-path identifiers ...)
                 (begin
                   (require plugin-path
                            (only-in identifiers ...))
                   (provide identifiers ...))]))
        */
        // This will fail to compile - anything that expands into a require will fail since
        // require is more or less a top level primitive. What we need to do is figure
        // out a way to have this be recursive - the whole compilation step should
        // go again once we discover that there is another require. It shouldn't be too bad,
        // but the base case has to be figured out such that we don't get infinite recursion.
        // I think the condition is probably something along the following:
        //
        // - Did we expand anything
        // - Are there require statements
        //
        // If we expanded anything, we then should check for require statements... maybe

        let mut new_exprs = Vec::new();

        // self.source_ast.pretty_print();

        self.collect_requires()?;

        self.collect_provides()?;

        // if log_enabled!(log::Level::Info) {
        // debug!(target: "requires", "Requires: {:#?}", self.require_objects);
        // debug!(target: "requires", "Provides: {:#?}", self.provides);
        // debug!(target: "requires", "Provides for-syntax: {:?}", self.provides_for_syntax);
        // }

        if self.visited.contains(&self.name) {
            stop!(Generic => format!("circular dependency found during module resolution with: {:?}", self.name))
        }

        self.visited.insert(self.name.clone());

        if self.main {
            let exprs = core::mem::take(&mut self.source_ast);
            self.source_ast = exprs
                .into_iter()
                .filter(|x| {
                    if let ExprKind::List(l) = x {
                        if let Some(provide) = l.first_ident() {
                            return *provide != *PROVIDE;
                        }
                    }
                    true
                })
                .collect();
        }

        self.extract_macro_defs()?;

        // TODO include built ins here
        if self.require_objects.is_empty() && !self.main {
            // We're at a leaf, put into the cache
            new_exprs.push(self.compile_module()?);
        } else {
            // TODO come back for parsing built ins
            let requires = self.require_objects.clone();
            for module in requires
                .iter()
                .filter(|x| matches!(x.path, PathOrBuiltIn::BuiltIn(_)))
                .map(|x| x.path.get_path())
            {
                // We've established nothing has changed with this file
                // Check to see if its in the cache first
                // Otherwise go ahead and compile
                // If we already have compiled this module, get it from the cache
                if let Some(_m) = self.compiled_modules.compiled_modules.get(module.as_ref()) {
                    // dbg!("Getting {:?} from the module cache", module);
                    // println!("Already found in the cache: {:?}", module);
                    // new_exprs.push(m.to_module_ast_node());
                    // No need to do anything
                    continue;
                }

                let mut new_module = self.load_required(&PathOrBuiltIn::BuiltIn(
                    module.to_str().unwrap().to_owned().into(),
                ))?;

                // Walk the tree and compile any dependencies
                // This will eventually put the module in the cache
                let mut module_exprs = new_module.compile()?;

                new_exprs.append(&mut module_exprs);

                // Probably want to evaluate a module even if it has no provides?
                if !new_module.provides.is_empty() {
                    new_exprs.push(new_module.compile_module()?);
                } else if !new_module
                    .compiled_modules
                    .compiled_modules
                    .contains_key(&new_module.name)
                {
                    new_exprs.push(new_module.compile_module()?);
                }
            }

            // At this point, requires should be fully qualified (absolute) paths

            for (module, require_statement_span) in requires
                .iter()
                .filter(|x| matches!(x.path, PathOrBuiltIn::Path(_)))
                .map(|x| (x.path.get_path(), x.span))
            {
                if cfg!(target_family = "wasm") {
                    stop!(Generic => "requiring modules is not supported for wasm");
                }

                let last_modified = std::fs::metadata(module.as_ref())
                    .map_err(|err| {
                        let mut err = crate::SteelErr::from(err);
                        err.prepend_message(&format!(
                            "Attempting to load module from: {:?} ",
                            module
                        ));
                        err.set_span(require_statement_span)
                    })?
                    .modified()?;

                // Check if we should compile based on the last time modified
                // If we're unable to get information, we want to compile
                let should_recompile =
                    if let Some(cached_modified) = self.file_metadata.get(module.as_ref()) {
                        last_modified != *cached_modified
                    } else {
                        true
                    };

                let mut downstream_validated = true;

                // We've established nothing has changed with this file
                // Check to see if its in the cache first
                // Otherwise go ahead and compile
                if !should_recompile {
                    // If we already have compiled this module, get it from the cache
                    if let Some(m) = self.compiled_modules.get(module.as_ref(), self.sources) {
                        // debug!("Getting {:?} from the module cache", module);
                        // println!("Already found in the cache: {:?}", module);
                        // new_exprs.push(m.to_module_ast_node());
                        // No need to do anything

                        // Check the dependencies all the way down.
                        // if any are invalidated, re-compile the whole thing.
                        let mut stack = m.downstream.clone();

                        while let Some(next) = stack.pop() {
                            let meta = std::fs::metadata(&next)?;

                            if let Some(prev) = self.file_metadata.get(&next) {
                                if *prev != meta.modified()? {
                                    // println!(
                                    //     "Detected change in {:?}, recompiling root starting from {:?}",
                                    //     next,
                                    //     module.as_ref()
                                    // );
                                    downstream_validated = false;
                                    break;
                                }
                            }

                            if let Some(module) = self.compiled_modules.get(&next, self.sources) {
                                for child in &module.downstream {
                                    stack.push(child.to_owned());
                                }
                            }
                        }

                        if downstream_validated {
                            continue;
                        }
                    }
                }

                // TODO: Parallelize this?
                // There is quite the opportunity to parallelize a chunk
                // of the compilation.

                let mut new_module =
                    self.load_required(&PathOrBuiltIn::Path(module.into_owned()))?;

                // Walk the tree and compile any dependencies
                // This will eventually put the module in the cache
                let mut module_exprs = new_module.compile()?;

                new_exprs.append(&mut module_exprs);

                // If we need to, revisit because there are new provides
                if !new_module.provides.is_empty() {
                    new_exprs.push(new_module.compile_module()?);
                // If the module hasn't yet been compiled, compile it anyway
                } else if !new_module
                    .compiled_modules
                    .compiled_modules
                    .contains_key(&new_module.name)
                {
                    // else if !new_module.compiled_modules.contains_key(&new_module.name) {
                    new_exprs.push(new_module.compile_module()?);
                } else if !downstream_validated {
                    new_exprs.push(new_module.compile_module()?);
                }
            }
        }

        // log::info!("Compiling module: {:?} took {:?}", self.name, now.elapsed());
        // new_exprs.pretty_print();

        Ok(new_exprs)
    }

    // TODO: This should run again on itself, probably
    fn compile_module(&mut self) -> Result<ExprKind> {
        let mut ast = core::mem::take(&mut self.source_ast);
        let mut provides = core::mem::take(&mut self.provides);
        // Clone the requires... I suppose
        let requires = self.require_objects.clone();

        // info!(
        //     target: "requires",
        //     "Into compiled module: provides for syntax: {:?}",
        //     self.provides_for_syntax
        // );

        let prev_length = ast.len();

        // Attempt extracting the syntax transformers from this module
        if let Some(kernel) = self.kernel.as_mut() {
            kernel.load_syntax_transformers(&mut ast, self.name.to_str().unwrap().to_string())?
        };

        let loaded_syntax_transformers = prev_length != ast.len();

        // Native heads see only the definitions before them, while bodies see every definition.
        // Only native forms without a kernel need the imported bindings.
        let mut native_heads = FxHashSet::default();
        let native_requires = match self.kernel {
            None => self.require_objects.as_slice(),
            Some(_) => &[],
        };
        for require in native_requires {
            let module = self
                .compiled_modules
                .compiled_modules
                .get(require.path.get_path().as_ref())
                .unwrap();
            imported_bindings(
                require,
                &module.provides,
                &module.provides_for_syntax,
                &module.macro_map,
                |name, smacro| {
                    if smacro.is_none() {
                        native_heads.insert(name);
                    }
                },
            );
        }
        let mut global_defs = collect_globals(&ast);
        global_defs.extend(native_heads.iter().copied());
        // Native definitions are module globals too, so module macro templates can reference
        // them, unless an import or an earlier definition shadows their head.
        let no_kernel = self.kernel.is_none();
        predeclare_native_definitions(
            &ast,
            &|name| native_heads.contains(name),
            GlobalMap::Set(&FxHashSet::default()),
            &|name| {
                self.macro_map.contains_key(name)
                    || no_kernel && self.global_macro_map.contains_key(name)
            },
            None,
            &mut |name| {
                global_defs.insert(name);
            },
        );
        let mut native_globals = global_defs.clone();
        let imported_bindings = native_heads.clone();
        let globals = GlobalMap::Set(&global_defs);

        // TODO: Revisit if caching is something we want here
        // if self.kernel.is_some() && !loaded_syntax_transformers {
        //     let modules = self.compiled_modules.compiled_modules.clone();
        //     if let Some(module) = self.compiled_modules.cached_mut(&self.name, self.sources) {
        //         log::info!("Using cached module: {:?}", self.name);

        //         module.set_emitted(true);

        //         let top_level_time = crate::time::Instant::now();

        //         let res = module.to_top_level_module(&modules, self.global_macro_map);

        //         log::info!("Cached top level time: {:?}", top_level_time.elapsed());

        //         log::info!("Using cached module took: {:?}", now.elapsed());

        //         return res;
        //     } else {
        //         log::info!("Module not found in the cache: {:?}", self.name);
        //     }
        // }

        // This needs to be overlayed with imported macros. So the idea being that this
        // expansion _also_ interweaves with the other requires... seems to make sense.
        //
        // And it also seems like it needs to happen at the same time. So the lookups
        // should happen together.

        if self.require_objects.is_empty() && self.kernel.is_some() {
            for expr in &mut ast {
                expand(expr, &self.macro_map, globals)?;
                expand_kernel_in_env(
                    expr,
                    self.kernel.as_mut(),
                    self.builtin_modules.clone(),
                    self.name.to_str().unwrap(),
                    GlobalMap::Scoped(&self.global_bindings, &native_globals),
                )?;
                collect_defines(std::slice::from_ref(expr), &mut |name| {
                    native_globals.insert(name);
                });
                expand_module_scoped(expr, &self.macro_map, globals)?;
            }
        }

        // TODO: Provides also need to have this kind of macro expansion as the above!
        for expr in provides.iter_mut() {
            expand(expr, &self.macro_map, globals)?;
            // .and_then(|x| {
            // expand_kernel(x, self.kernel.as_mut(), self.builtin_modules.clone())
            expand_kernel_in_env(
                expr,
                self.kernel.as_mut(),
                self.builtin_modules.clone(),
                // Expanding macros in the environment?
                self.name.to_str().unwrap(),
                GlobalMap::Scoped(&self.global_bindings, &native_globals),
            )?;
            // })
        }

        let mut mangled_asts = Vec::with_capacity(ast.len() + 16);
        let mut downstream = Vec::new();
        let mut downstream_builtins = Vec::new();

        let mut required_macros = Vec::new();

        let macro_map = Arc::make_mut(&mut self.macro_map);

        for require_object in self.require_objects.iter() {
            let require_for_syntax = require_object.path.get_path();

            if let PathOrBuiltIn::Path(_) = &require_object.path {
                downstream.push(require_for_syntax.clone().into_owned());
            }

            if let PathOrBuiltIn::BuiltIn(_) = &require_object.path {
                downstream_builtins.push(require_for_syntax.clone().into_owned());
            }

            // Stash this?
            let (module, in_scope_macros, name_mangler) = ModuleManager::find_in_scope_macros(
                &mut self.compiled_modules,
                require_for_syntax.as_ref(),
                require_object,
                &mut mangled_asts,
            );

            required_macros.push(RequiredModuleMacros {
                module_key: require_for_syntax.clone().into_owned(),
                module_macros: module.macro_map.clone(),
                in_scope_macros,
                name_mangler,
                module_name: module.name.to_str().unwrap().to_owned(),
            });

            if require_object.idents_to_import.is_empty() {
                if let Some(m) = self
                    .compiled_modules
                    .get(&require_object.path.get_path(), self.sources)
                {
                    for provide_expr in &m.provides {
                        // TODO: Handle provide spec stuff!
                        for provide in &provide_expr.list().unwrap().args[1..] {
                            if let Some(ident) = provide.atom_identifier() {
                                macro_map.remove(ident);
                            }

                            if let Some(list) = provide.list().and_then(|x| x.second_ident()) {
                                macro_map.remove(list);
                            }
                        }
                    }
                }
            }
        }

        let overlays = required_macros
            .iter_mut()
            .map(|x| RequiredMacroMap {
                map: x,
                changed: false,
            })
            .collect::<Vec<_>>();

        let replay_macros = macro_map.clone();
        let mut many_expander = ExpanderMany::new(macro_map, overlays, globals);
        many_expander.global_macro_map = Some(self.global_macro_map);
        let is_macro = |expander: &ExpanderMany, name: &InternedString| {
            expander.map.contains_key(name)
                || self.global_macro_map.contains_key(name)
                || expander
                    .overlays
                    .iter()
                    .any(|overlay| overlay.map.in_scope_macros.contains_key(name))
        };

        // Without a kernel, `native_globals` is first read by the deferred pass below, which
        // predeclares native definitions once module macros have expanded.
        let prepare_heads = self.kernel.is_none();
        let mut prepared = 0;
        // Top-level definitions shadow module and imported macros in the deferred statements after
        // them, as they do in the deferred pass.
        let mut top_level_definitions = FxHashSet::default();
        for index in 0..ast.len() {
            if prepare_heads && index == prepared {
                prepared = prepare_native_heads(
                    &mut ast,
                    index,
                    self.global_bindings,
                    &mut native_heads,
                    &mut native_globals,
                    &|name| is_macro(&many_expander, name),
                )?;
            }
            let defer_body = prepare_heads && index >= prepared;
            if defer_body {
                many_expander.expand_top_level(&mut ast[index], &mut top_level_definitions)?;
            } else {
                many_expander.expand(&mut ast[index])?;
            }

            // A macro call stopped preparation, so prepare its expansion.
            if prepare_heads && index == prepared {
                prepared = prepare_native_heads(
                    &mut ast,
                    index,
                    self.global_bindings,
                    &mut native_heads,
                    &mut native_globals,
                    &|name| is_macro(&many_expander, name),
                )?;
            }
            let expr = &mut ast[index];

            if self.kernel.is_some() {
                expand_kernel_in_env(
                    expr,
                    self.kernel.as_mut(),
                    self.builtin_modules.clone(),
                    // Expanding macros in the environment?
                    self.name.to_str().unwrap(),
                    GlobalMap::Scoped(&self.global_bindings, &native_globals),
                )?;
            }
            collect_defines(std::slice::from_ref(expr), &mut |name| {
                native_heads.insert(name);
                native_globals.insert(name);
                top_level_definitions.insert(name);
            });

            if !defer_body {
                expand_module_scoped(expr, &many_expander.map, globals)?;
            }

            for RequiredMacroMap {
                changed,
                map: req_macro,
            } in many_expander.overlays.iter_mut()
            {
                if *changed {
                    expand_module_scoped(expr, &req_macro.module_macros, globals)?;

                    // Expanding the kernel with only these macros...
                    let local_changed = self.kernel.is_some()
                        && expand_kernel_in_env_with_change(
                            expr,
                            self.kernel.as_mut(),
                            // We don't need to expand those here
                            ModuleContainer::default(),
                            &req_macro.module_name,
                            GlobalMap::Scoped(&self.global_bindings, &native_globals),
                        )?;
                    collect_defines(std::slice::from_ref(expr), &mut |name| {
                        native_heads.insert(name);
                        native_globals.insert(name);
                    });

                    if local_changed {
                        req_macro.name_mangler.visit(expr);
                    }

                    *changed = false;
                }
            }
        }

        if self.kernel.is_none() {
            flatten_module_begins(&mut ast)?;
            many_expander.reset_for_replay(&replay_macros, &imported_bindings);
            // Later module and imported macros can define names that shadow global macros.
            collect_defines(&ast, &mut |name| {
                native_globals.insert(name);
            });
            let mut native_heads = imported_bindings;
            let is_macro = |name: &InternedString| self.global_macro_map.contains_key(name);
            predeclare_native_bindings(
                &ast,
                self.global_bindings,
                &native_heads,
                &mut native_globals,
                &is_macro,
                &self.builtin_modules,
            );
            let mut prepared = 0;
            for index in 0..ast.len() {
                if index >= prepared {
                    prepared = prepare_native_heads(
                        &mut ast,
                        index,
                        self.global_bindings,
                        &mut native_heads,
                        &mut native_globals,
                        &is_macro,
                    )?;
                }
                // Flattened statements still share their preceding value bindings.
                many_expander.expand_in_scope(&mut ast[index])?;
                for overlay in &mut many_expander.overlays {
                    if overlay.changed {
                        expand_module_scoped(&mut ast[index], &overlay.map.module_macros, globals)?;
                        overlay.changed = false;
                    }
                }
                Expander::expand_global_macros(
                    &mut ast[index],
                    self.global_macro_map,
                    self.global_bindings,
                    &mut native_globals,
                    &self.builtin_modules,
                    false,
                )?;
                if index >= prepared {
                    prepared = prepare_native_heads(
                        &mut ast,
                        index,
                        self.global_bindings,
                        &mut native_heads,
                        &mut native_globals,
                        &is_macro,
                    )?;
                }
                expand_kernel_in_env(
                    &mut ast[index],
                    None,
                    self.builtin_modules.clone(),
                    self.name.to_str().unwrap(),
                    GlobalMap::Scoped(&self.global_bindings, &native_globals),
                )?;
                collect_defines(std::slice::from_ref(&ast[index]), &mut |name| {
                    native_heads.insert(name);
                    native_globals.insert(name);
                    many_expander.in_scope_values.define(name);
                    many_expander.map.remove(&name);
                });
            }
        }

        for req_macro in &mut required_macros {
            for expr in provides.iter_mut() {
                // First expand the in scope macros
                // These are macros

                let exclusions = HashSet::new();

                let mut expander = Expander::new(&req_macro.in_scope_macros, &exclusions, globals);
                expander.expand(expr)?;

                if expander.changed {
                    expand(expr, &req_macro.module_macros, globals)?;
                }
            }
        }
        retain_imported_macros(
            &mut self.macro_map,
            &required_macros,
            &native_globals,
            &self.name,
            self.provides_for_syntax
                .iter()
                .filter_map(ExprKind::atom_identifier)
                .chain(provides.iter().flat_map(|provide| {
                    provide.list().unwrap().args[1..]
                        .iter()
                        .filter_map(ExprKind::atom_identifier)
                })),
        );

        // TODO: Check HERE for whether there are more requires than were previously found.
        // If so, we should go back and compile the module again

        for expr in &mut ast {
            lower_entire_ast(expr)?;
            FlattenBegin::flatten(expr);
        }

        // And then finally, expand the keyword arguments:
        for expr in &mut ast {
            expand_kernel_in_env(
                expr,
                self.kernel.as_mut(),
                self.builtin_modules.clone(),
                self.name.to_str().unwrap(),
                GlobalMap::Scoped(&self.global_bindings, &native_globals),
            )?;
            collect_defines(std::slice::from_ref(expr), &mut |name| {
                native_globals.insert(name);
            });
        }

        // TODO: @Matt - fix this hack
        {
            self.source_ast = ast;
            self.provides = provides;

            self.collect_provides()?;

            provides = core::mem::take(&mut self.provides);
            ast = core::mem::take(&mut self.source_ast);
        }

        // Put the mangled asts at the top
        // then include the ast there
        // mangled_asts.append(&mut ast);

        for expr in mangled_asts.iter_mut() {
            lower_entire_ast(expr)?;

            FlattenBegin::flatten(expr);
        }

        mangled_asts.append(&mut ast);

        // TODO: @Matt: 7/3/25
        // Re-exporting macros needs to work here
        let mut module = CompiledModule::new(
            self.name.clone(),
            provides,
            requires,
            self.provides_for_syntax
                .iter()
                .map(|x| *x.atom_identifier().unwrap())
                .collect(),
            // core::mem::take(&mut self.macro_map),
            self.macro_map.clone(),
            mangled_asts,
            downstream,
            downstream_builtins,
        );

        module.set_emitted(true);

        // Cache it
        if !loaded_syntax_transformers
            && module.provides_for_syntax.is_empty()
            && self.local_macros.is_empty()
            && module.get_provides().iter().all(|x| {
                if let ExprKind::List(l) = x {
                    let mut iter = l.args.iter();
                    iter.next();

                    for provide in iter {
                        if let Some(ident) = provide.atom_identifier() {
                            if self.local_macros.contains(ident) {
                                return false;
                            }
                        } else {
                            return false;
                        }
                    }

                    return true;
                }

                true
            })
        {
            // Remove the unused defines since this module
            // won't need to reference these later from any macros
            {
                let mut sem = SemanticAnalysis::new(&mut module.ast);
                sem.remove_unused_define_imports();
            }

            // TODO: Revisit with some caching later
            // self.compiled_modules.cache_module(&module.name, &module);
        }

        let result = module.to_top_level_module(
            &self.compiled_modules.compiled_modules,
            self.global_macro_map,
        )?;

        self.compiled_modules
            .compiled_modules
            .insert(self.name.clone(), module);

        Ok(result)
    }

    fn extract_macro_defs(&mut self) -> Result<()> {
        // Probably don't have more than 128 macros in a module, but who knows?
        // let mut macro_indices = SmallVec::<[usize; 128]>::new();

        // let exprs = core::mem::take(&mut self.source_ast);

        let mut error = None;

        self.source_ast.retain_mut(|expr| {
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

                            self.local_macros.insert(*name);

                            Arc::make_mut(&mut self.macro_map).insert(*name, generated_macro);
                        }
                        Err(e) => {
                            if error.is_none() {
                                error = Some(e);
                            }
                            // error = Some(e);
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

    // Takes out the (for-syntax) forms from the provides
    fn filter_out_for_syntax_provides(
        &mut self,
        exprs: ThinVec<ExprKind>,
    ) -> Result<ThinVec<ExprKind>> {
        let mut normal_provides = ThinVec::new();

        for expr in exprs {
            match &expr {
                ExprKind::Atom(_) => {
                    normal_provides.push(expr);
                }
                ExprKind::List(l) => {
                    if let Some(for_syntax) = l.first_ident() {
                        match *for_syntax {
                            x if x == *FOR_SYNTAX => {
                                if l.args.len() != 2 {
                                    stop!(ArityMismatch => "provide expects a single identifier in the (for-syntax <ident>)"; l.location)
                                }

                                // Collect the for syntax expressions
                                // TODO -> remove this clone
                                self.provides_for_syntax.push(l.args[1].clone());
                            }
                            x if x == *REQUIRE_IDENT_SPEC => {
                                normal_provides.push(expr);
                            }
                            // x if x == *CONTRACT_OUT || x == *REQUIRE_IDENT_SPEC => {
                            //     normal_provides.push(expr);
                            // }
                            _ => {
                                normal_provides.push(expr);
                                // stop!(TypeMismatch => "provide expects either an identifier, (for-syntax <ident>), or (contract/out ...)")
                            }
                        }
                    } else {
                        stop!(TypeMismatch => "provide expects either an identifier or a (for-syntax <ident>)"; l.location)
                    }
                }
                _ => {
                    stop!(TypeMismatch => "provide expects either a (for-syntax <ident>) or an ident"; expr.span())
                }
            }
        }

        Ok(normal_provides)
    }

    // TODO -> collect (provide (for-syntax ...))
    // I think these will already be collected for the macro, however I think for syntax should be found earlier
    // Otherwise the macro expansion will not be able to understand it
    fn collect_provides(&mut self) -> Result<()> {
        // let now = crate::time::Instant::now();

        let mut non_provides = Vec::with_capacity(self.source_ast.len());
        let exprs = core::mem::take(&mut self.source_ast);

        fn walk(
            module_builder: &mut ModuleBuilder,
            exprs: Vec<ExprKind>,
            non_provides: &mut Vec<ExprKind>,
        ) -> Result<()> {
            for mut expr in exprs {
                match &mut expr {
                    ExprKind::List(l) => {
                        if let Some(provide) = l.first_ident() {
                            if *provide == *PROVIDE {
                                if l.len() == 1 {
                                    stop!(Generic => "provide expects at least one identifier to provide"; l.location);
                                }

                                // Swap out the value inside the list
                                let args = core::mem::take(&mut l.args);

                                let filtered =
                                    module_builder.filter_out_for_syntax_provides(args)?;

                                l.args = filtered;

                                module_builder.provides.push(expr);

                                continue;
                            }
                        }
                    }
                    ExprKind::Begin(b) => {
                        let exprs = core::mem::take(&mut b.exprs);

                        // Reserve capacity for these to be moved to the top level
                        non_provides.reserve(exprs.len());

                        walk(module_builder, exprs, non_provides)?;
                    }
                    _ => {}
                }

                non_provides.push(expr);
            }

            Ok(())
        }

        walk(self, exprs, &mut non_provides)?;

        self.source_ast = non_provides;

        // log::debug!(target: "pipeline_time", "Collecting provides time: {:?}", now.elapsed());

        Ok(())
    }

    fn parse_require_object(
        &mut self,
        home: &Option<PathBuf>,
        r: &crate::parser::ast::Require,
        atom: &ExprKind,
    ) -> Result<RequireObject> {
        let mut object = RequireObjectBuilder::default();

        // Set the span so we can pass through an error if the
        // module is not found
        object.span = r.location.span;

        self.parse_require_object_inner(home, r, atom, &mut object)
            .and_then(|_| object.build())
    }

    // TODO: Recursively crunch the requires to gather up the necessary information
    fn parse_require_object_inner(
        &mut self,
        home: &Option<PathBuf>,
        r: &crate::parser::ast::Require,
        atom: &ExprKind,
        require_object: &mut RequireObjectBuilder,
    ) -> Result<()> {
        log::info!("Parsing require object from: {:?}", self.name);
        match atom {
            ExprKind::Atom(Atom {
                syn:
                    SyntaxObject {
                        ty: TokenType::StringLiteral(s),
                        span,
                        ..
                    },
            }) => {
                if require_object.path.is_some() {
                    stop!(Generic => "require object only expects one path!")
                }

                // Try this?
                if let Some(lib) = BUILT_INS.iter().cloned().find(|x| x.0 == s.resolve()) {
                    require_object.path = Some(PathOrBuiltIn::BuiltIn(lib.0.into()));
                    return Ok(());
                }

                if self.custom_builtins.contains_key(s.resolve()) {
                    require_object.path =
                        Some(PathOrBuiltIn::BuiltIn(s.clone().to_string().into()));

                    return Ok(());
                }

                if self
                    .module_resolvers
                    .iter()
                    .find(|x| x.exists(s.resolve()))
                    .is_some()
                {
                    require_object.path =
                        Some(PathOrBuiltIn::BuiltIn(s.clone().to_string().into()));

                    return Ok(());
                }

                if cfg!(target_family = "wasm") {
                    stop!(Generic => "requiring modules is not supported for wasm");
                }

                let mut current = self.name.clone();
                if current.is_file() {
                    current.pop();
                }
                current.push(PathBuf::from(s.resolve()));

                // // If the path exists on its own, we can continue
                // // But theres the case where we're searching for a module on the STEEL_HOME
                if !current.exists() {
                    if let Some(mut home) = home.clone() {
                        home.push(PathBuf::from(s.resolve()));
                        current = home;

                        log::info!("Searching STEEL_HOME for {:?}", current);

                        if !current.exists() {
                            for dir in self.search_dirs {
                                let mut dir = dir.clone();
                                dir.push(s.resolve());

                                if dir.exists() {
                                    current = dir;
                                    break;
                                }
                            }
                        }
                    } else {
                        // TODO: Check if this module exists in STEEL_HOME first. If it does, we'll take that as our candidate
                        // and then continue on to the final module resolution part.
                        //
                        // If it doesn't exist, we should iterate through the search directories and attempt to find
                        // a matching path there.
                        for dir in self.search_dirs {
                            let mut dir = dir.clone();
                            dir.push(s.resolve());

                            if dir.exists() {
                                current = dir;
                                break;
                            }
                        }

                        stop!(Generic => format!("Module not found: {:?} with STEEL_HOME: {:?}", current, home); *span)
                    }
                }

                // Get the absolute path and store that
                // self.requires.push(current)

                let current = try_canonicalize(current);

                require_object.path = Some(PathOrBuiltIn::Path(current));
            }

            // TODO: Requires with qualifiers, that aren't just for-syntax
            // Perhaps like:
            // (with-prefix <xyz>)
            ExprKind::List(l) => {
                match l.first_ident() {
                    Some(x) if *x == *ONLY_IN => {
                        if l.args.len() < 2 {
                            stop!(BadSyntax => "only-in expects a require-spec and optionally a list of ids to bind (maybe renamed)"; l.location);
                        }

                        self.parse_require_object_inner(home, r, &l.args[1], require_object)?;

                        for remaining in &l.args[2..] {
                            match remaining {
                                ExprKind::Atom(_) => {
                                    if remaining.atom_identifier().is_none() {
                                        stop!(BadSyntax => "only-in expected an identifier to import"; remaining.span());
                                    }
                                    require_object
                                        .idents_to_import
                                        .push(MaybeRenamed::Normal(remaining.clone()));
                                }
                                ExprKind::List(l) => {
                                    if l.len() != 2 {
                                        stop!(BadSyntax => "Expected a pair when renaming required identifiers");
                                    }

                                    let from = &l.args[0];
                                    let to = &l.args[1];

                                    if from.atom_identifier().is_none()
                                        || to.atom_identifier().is_none()
                                    {
                                        stop!(BadSyntax => "only-in expected identifiers to rename");
                                    }

                                    // (<from> <to>)
                                    require_object
                                        .idents_to_import
                                        .push(MaybeRenamed::Renamed(from.clone(), to.clone()));
                                }
                                _ => {
                                    stop!(BadSyntax => "unexpected syntax in only-in form during module requires")
                                }
                            }
                        }
                    }

                    Some(x) if *x == *PREFIX_IN => {
                        if l.args.len() != 3 {
                            stop!(BadSyntax => "prefix-in expects a prefix to prefix a given file or module"; l.location);
                        }

                        let prefix = &l.args[1];

                        if let Some(prefix) = prefix.atom_identifier() {
                            match &mut require_object.prefix {
                                Some(existing_prefix) => {
                                    // Append the new symbol to the existing prefix
                                    existing_prefix.push_str(prefix.resolve());
                                }
                                None => {
                                    require_object.prefix = Some(prefix.resolve().to_string());
                                }
                            }

                            self.parse_require_object_inner(home, r, &l.args[2], require_object)?;
                        } else {
                            stop!(TypeMismatch => "prefix-in expects an identifier to use for the prefix"; prefix.span());
                        }
                    }

                    Some(x) if *x == *FOR_SYNTAX => {
                        // We're expecting something like (for-syntax "foo")
                        if l.args.len() != 2 {
                            stop!(BadSyntax => "for-syntax expects one string literal referring to a file or module"; l.location);
                        }

                        let mod_name = &l.args[1];
                        if let Some(path) = mod_name.string_literal() {
                            if let Some(lib) = BUILT_INS.iter().find(|x| x.0 == path) {
                                // self.built_ins.push(PathBuf::from(lib.0));

                                require_object.path = Some(PathOrBuiltIn::BuiltIn(lib.0.into()));
                                require_object.for_syntax = true;

                                return Ok(());
                                // continue;
                            } else if self.custom_builtins.contains_key(path) {
                                require_object.path =
                                    Some(PathOrBuiltIn::BuiltIn(Cow::Owned(path.to_string())));
                                require_object.for_syntax = true;

                                return Ok(());
                            } else if self
                                .module_resolvers
                                .iter()
                                .find(|x| x.exists(path))
                                .is_some()
                            {
                                require_object.path =
                                    Some(PathOrBuiltIn::BuiltIn(Cow::Owned(path.to_string())));
                                require_object.for_syntax = true;
                            } else {
                                let mut current = self.name.clone();
                                if current.is_file() {
                                    current.pop();
                                }
                                current.push(PathBuf::from(path));

                                if !current.exists() {
                                    if let Some(mut home) = home.clone() {
                                        home.push(PathBuf::from(path));
                                        current = home;

                                        if !current.exists() {
                                            for dir in self.search_dirs {
                                                let mut dir = dir.clone();
                                                dir.push(path);

                                                if dir.exists() {
                                                    current = dir;
                                                    break;
                                                }
                                            }
                                        }

                                        log::info!("Searching STEEL_HOME for {:?}", current);
                                    } else {
                                        for dir in self.search_dirs {
                                            let mut dir = dir.clone();
                                            dir.push(path);

                                            if dir.exists() {
                                                current = dir;
                                                break;
                                            }
                                        }

                                        stop!(Generic => format!("Module not found: {:?}", current); mod_name.span())
                                    }
                                }

                                require_object.for_syntax = true;
                                let current = try_canonicalize(current);
                                require_object.path = Some(PathOrBuiltIn::Path(current));
                            }
                        } else {
                            stop!(BadSyntax => "for-syntax expects a string literal referring to a file or module"; mod_name.span());
                        }
                    }
                    _ => {
                        stop!(BadSyntax => "require accepts either a string literal, a for-syntax expression or an only-in expression"; l.location)
                    }
                }
            }

            unknown => {
                stop!(Generic => format!("require object expected a string literal referring to a file/module, found: {}", unknown); atom.span())
            }
        }

        Ok(())
    }

    fn collect_requires(&mut self) -> Result<()> {
        // unimplemented!()

        let mut exprs_without_requires = Vec::new();
        let exprs = core::mem::take(&mut self.source_ast);

        let home = STEEL_HOME
            .clone()
            .map(|x| {
                // TODO: Fix this - try to hack in a root drive
                // for windows if a unix path is provided
                if cfg!(target_os = "windows") {
                    let mut result = x.trim_start_matches("/").to_string();

                    let mut iter = result.chars();
                    iter.next();
                    if matches!(iter.next(), Some(':')) {
                        return PathBuf::from(result);
                    }

                    result.insert(1, ':');
                    return PathBuf::from(result);
                }

                PathBuf::from(x)
            })
            .map(|mut x| {
                x.push("cogs");

                x
            });

        fn walk(
            module_builder: &mut ModuleBuilder,
            home: &Option<PathBuf>,
            exprs_without_requires: &mut Vec<ExprKind>,
            exprs: Vec<ExprKind>,
        ) -> Result<()> {
            for expr in exprs {
                match expr {
                    // Include require/for-syntax here
                    // This way we have some understanding of what dependencies a file has
                    ExprKind::Require(r) => {
                        for atom in &r.modules {
                            // TODO: Consider making this not a reference for r
                            let require_object =
                                module_builder.parse_require_object(home, &r, atom)?;

                            module_builder.require_objects.push(require_object);
                        }
                    }
                    ExprKind::Begin(b) => {
                        walk(module_builder, home, exprs_without_requires, b.exprs)?
                    }
                    _ => exprs_without_requires.push(expr),
                }
            }

            Ok(())
        }

        walk(self, &home, &mut exprs_without_requires, exprs)?;

        self.source_ast = exprs_without_requires;
        Ok(())
    }

    fn new_from_path(
        name: PathBuf,
        compiled_modules: &'a mut CompiledModuleCache,
        visited: &'a mut FxHashSet<PathBuf>,
        file_metadata: &'a mut crate::HashMap<PathBuf, SystemTime>,
        sources: &'a mut Sources,
        kernel: &'a mut Option<Kernel>,
        builtin_modules: ModuleContainer,
        global_macro_map: &'a FxHashMap<InternedString, SteelMacro>,
        global_bindings: GlobalMap<'a>,
        custom_builtins: &'a HashMap<String, String>,
        search_dirs: &'a [PathBuf],
        module_resolvers: &'a [Arc<dyn SourceModuleResolver>],
        prelude_string: &'a str,
    ) -> Result<Self> {
        ModuleBuilder::raw(
            name,
            compiled_modules,
            visited,
            file_metadata,
            sources,
            kernel,
            builtin_modules,
            global_macro_map,
            global_bindings,
            custom_builtins,
            search_dirs,
            module_resolvers,
            true,
            prelude_string,
        )
        .parse_from_path()
    }

    fn raw(
        name: PathBuf,
        compiled_modules: &'a mut CompiledModuleCache,
        visited: &'a mut FxHashSet<PathBuf>,
        file_metadata: &'a mut crate::HashMap<PathBuf, SystemTime>,
        sources: &'a mut Sources,
        kernel: &'a mut Option<Kernel>,
        builtin_modules: ModuleContainer,
        global_macro_map: &'a FxHashMap<InternedString, SteelMacro>,
        global_bindings: GlobalMap<'a>,
        custom_builtins: &'a HashMap<String, String>,
        search_dirs: &'a [PathBuf],
        module_resolvers: &'a [Arc<dyn SourceModuleResolver>],
        canonicalize: bool,
        prelude_string: &'a str,
    ) -> Self {
        // println!("New module found: {:?}", name);

        let name = if canonicalize {
            try_canonicalize(name)
        } else {
            name
        };

        ModuleBuilder {
            name,
            main: false,
            local_macros: FxHashSet::default(),
            source_ast: Vec::new(),
            // TODO: This used to be empty
            macro_map: default_prelude_macros(),
            require_objects: Vec::new(),
            provides: Vec::new(),
            provides_for_syntax: Vec::new(),
            compiled_modules,
            visited,
            file_metadata,
            sources,
            kernel,
            builtin_modules,
            global_macro_map,
            global_bindings,
            custom_builtins,
            search_dirs,
            module_resolvers,
            prelude_string,
            parsed_requires: FxHashMap::default(),
        }
    }

    fn parse_builtin(mut self, input: Cow<'static, str>) -> Result<Self> {
        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        let id = self
            .sources
            .add_source(input.clone(), Some(self.name.clone()));

        let parsed = Parser::new_from_source(&input, self.name.clone(), Some(id))
            .without_lowering()
            .map(|x| x.and_then(lower_macro_and_require_definitions))
            .collect::<core::result::Result<Vec<_>, ParseError>>()?;

        self.source_ast = parsed;

        #[cfg(feature = "profiling")]
        log::debug!(target: "pipeline_time", "Parsing: {:?} - {:?}", self.name, now.elapsed());

        // self.source_ast.pretty_print();

        Ok(self)
    }

    fn parse_from_path(mut self) -> Result<Self> {
        log::info!("Opening: {:?}", self.name);
        let mut exprs = String::new();

        // If we were unable to resolve it via any of the built in module resolvers,
        // then we check the file system.
        let mut file = std::fs::File::open(&self.name).map_err(|err| {
            let mut err = crate::SteelErr::from(err);
            err.prepend_message(&format!("Attempting to load module from: {:?} ", self.name));
            err
        })?;
        self.file_metadata
            .insert(self.name.clone(), file.metadata()?.modified()?);

        file.read_to_string(&mut exprs)?;

        let mut expressions = Parser::new(self.prelude_string, SourceId::none())
            .without_lowering()
            .map(|x| x.and_then(lower_macro_and_require_definitions))
            .collect::<core::result::Result<Vec<_>, ParseError>>()?;

        let id = self.sources.add_source(exprs, Some(self.name.clone()));

        {
            // Fetch the exprs after adding them to the sources
            // We did _just_ add it, so its fine to unwrap
            let guard = &self.sources.sources;

            let exprs = guard.get(id).unwrap();

            let mut parsed = Parser::new_from_source(exprs, self.name.clone(), Some(id))
                .without_lowering()
                .map(|x| x.and_then(lower_macro_and_require_definitions))
                .collect::<core::result::Result<Vec<_>, ParseError>>()?;

            expressions.append(&mut parsed);

            self.source_ast = expressions;
        }

        Ok(self)
    }
}
