#![allow(unused)]

use super::{
    builtin::{BuiltInModule, FunctionSignatureMetadata},
    primitives::{register_builtin_modules, CONSTANTS},
    vm::{SteelThread, Synchronizer, ThreadStateController},
};

#[cfg(feature = "dylibs")]
use super::{ffi::FFIModule, ffi::FFIWrappedModule};

#[cfg(feature = "dylibs")]
use super::dylib::DylibContainers;

use crate::{
    compiler::{
        compiler::{Compiler, SerializableCompiler},
        map::SymbolMap,
        modules::{
            intern_modules, path_to_module_name, CompiledModule, SourceModuleResolver,
            MANGLER_PREFIX, PRELUDE_WITHOUT_BASE,
        },
        program::{Executable, RawProgramWithSymbols, SerializableRawProgramWithSymbols},
    },
    containers::RegisterValue,
    core::{
        instructions::{pretty_print_dense_instructions, DenseInstruction, Instruction},
        labels::Expr,
    },
    gc::{
        shared::StandardShared,
        unsafe_erased_pointers::{
            BorrowedObject, CustomReference, OpaqueReferenceNursery, ReadOnlyBorrowedObject,
            ReferenceMarker,
        },
        Gc, Shared,
    },
    parser::{
        ast::ExprKind,
        expander::SteelMacro,
        interner::{get_interner, take_interner, InternedString},
        kernel::{fresh_kernel_image, Kernel},
        parser::{ParseError, Parser, Sources, SYNTAX_OBJECT_ID},
    },
    rerrs::{back_trace, back_trace_to_string},
    rvals::{
        AsRefMutSteelVal, AsRefSteelVal as _, FromSteelVal, IntoSteelVal, MaybeSendSyncStatic,
        Result, SteelString, SteelVal,
    },
    steel_vm::{
        builtin::{generate_function, register_context_functions},
        primitives::bootstrap_globals,
        register_fn::RegisterFn,
    },
    stop, throw,
    values::{
        closed::GlobalSlotRecycler,
        functions::{BoxedDynFunction, ByteCodeLambda},
    },
    SteelErr,
};
use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
    rc::Rc,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc, Mutex,
    },
};

use crate::values::HashMap as ImmutableHashMap;
use lasso::ThreadedRodeo;
use once_cell::sync::{Lazy, OnceCell};
use parking_lot::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use serde::{Deserialize, Serialize};
use steel_gen::OpCode;
use steel_parser::{
    ast::List,
    parser::{SourceId, SyntaxObject},
    tokens::{IntLiteral, TokenType},
};

#[cfg(all(feature = "sync", feature = "biased", not(feature = "triomphe")))]
use steel_rc::QueueHandle;

use crate::parser::ast::IteratorExtensions;

thread_local! {
    static KERNEL_BIN_FILE: Cell<Option<&'static [u8]>> = const { Cell::new(None) };
}

// Install the binary file to be used during bootup
// pub fn install_bin_file(bin: &'static [u8]) {
//     KERNEL_BIN_FILE.with(|x| x.set(Some(bin)));
// }

#[cfg(not(feature = "sync"))]
pub trait ModuleResolver {
    fn resolve(&self, name: &str) -> Option<BuiltInModule>;
    fn names(&self) -> Vec<String>;
}

#[cfg(feature = "sync")]
pub trait ModuleResolver: MaybeSendSyncStatic {
    fn resolve(&self, name: &str) -> Option<BuiltInModule>;
    fn names(&self) -> Vec<String>;
}

#[derive(Clone, Default)]
pub struct ModuleContainer {
    modules: Arc<RwLock<HashMap<Shared<str>, BuiltInModule>>>,
    // For modules that don't exist in memory. This could be useful for a world
    // in which a builtin module exists BUT we'd like to resolve the module for
    // inference purposes.
    unresolved_modules: Arc<RwLock<Option<StandardShared<dyn ModuleResolver>>>>,
}

impl ModuleContainer {
    pub fn with_expected_capacity() -> Self {
        Self {
            modules: Arc::new(RwLock::new(HashMap::with_capacity(48))),
            unresolved_modules: Default::default(),
        }
    }

    pub fn insert(&mut self, key: Shared<str>, value: BuiltInModule) {
        self.modules.write().insert(key, value);
    }

    pub fn get_doc(&self, key: &str) -> Option<String> {
        for module in self.modules.read().values() {
            let maybe_doc = module.get_documentation(key);

            if maybe_doc.is_some() {
                return maybe_doc;
            }
        }

        None
    }

    pub fn get_metadata_by_name(&self, key: &str) -> Option<FunctionSignatureMetadata> {
        for module in self.modules.read().values() {
            let maybe_meta = module.search_by_name(key);

            if maybe_meta.is_some() {
                return maybe_meta;
            }
        }

        None
    }

    pub fn get(&self, key: &str) -> Option<BuiltInModule> {
        let mut guard = self.modules.write();
        let found = guard.get(key).cloned();

        found.or_else(|| {
            let res = self
                .unresolved_modules
                .read()
                .as_ref()
                .and_then(|x| x.resolve(key));

            if let Some(res) = res {
                // Define the module now.
                guard.insert(Shared::from(key), res.clone());

                Some(res)
            } else {
                None
            }
        })
    }

    pub(crate) fn deep_clone(&self) -> Self {
        Self {
            modules: Arc::new(RwLock::new(self.modules.read().clone())),
            unresolved_modules: Arc::new(RwLock::new(self.unresolved_modules.read().clone())),
        }
    }

    pub fn inner(&self) -> RwLockReadGuard<'_, HashMap<Shared<str>, BuiltInModule>> {
        self.modules.read()
    }

    pub(crate) fn inner_mut(
        &mut self,
    ) -> RwLockWriteGuard<'_, HashMap<Shared<str>, BuiltInModule>> {
        self.modules.write()
    }

    pub fn with_resolver<T: ModuleResolver + 'static>(&mut self, resolver: T) {
        *self.unresolved_modules.write() = Some(StandardShared::new(resolver));
    }
}

#[derive(Debug)]
pub struct EngineStatistics {
    pub rooted_count: usize,
    pub constants_count: usize,
    pub sources_size: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct GlobalCheckpoint {
    symbol_map_offset: usize,
    globals_offset: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EngineId(pub(crate) usize);

impl EngineId {
    pub fn new() -> Self {
        static ENGINE_ID: AtomicUsize = AtomicUsize::new(0);
        let id = ENGINE_ID.fetch_add(1, Ordering::Relaxed);
        Self(id)
    }

    pub fn as_usize(self) -> usize {
        self.0
    }
}

/// Handle to a steel engine. This contains a main entrypoint thread, alongside
/// the compiler and all of the state necessary to keep a VM instance alive and
/// well.
pub struct Engine {
    pub(crate) virtual_machine: SteelThread,
    // TODO: Just put this, and all the other things,
    // inside the `SteelThread` - The compiler probably
    // still... needs to be shared, but thats fine.
    modules: ModuleContainer,
    #[cfg(feature = "dylibs")]
    dylibs: DylibContainers,
    pub(crate) id: EngineId,
}

impl Engine {
    pub fn enter_safepoint<T, F: FnMut() -> T>(&mut self, mut thunk: F) -> T {
        let mut res = None;

        self.virtual_machine
            .enter_safepoint(|_| -> Result<SteelVal> {
                res = Some((thunk)());
                Ok(SteelVal::Void)
            });

        res.unwrap()
    }
}

/*
#[cfg(feature = "biased")]
impl Drop for Engine {
    fn drop(&mut self) {
        steel_rc::QueueHandle::run_explicit_merge();
    }
}
*/

impl Clone for Engine {
    fn clone(&self) -> Self {
        let mut virtual_machine = self.virtual_machine.clone();

        virtual_machine.synchronizer = Synchronizer::for_current_thread();

        let compiler = Arc::new(RwLock::new(self.virtual_machine.compiler.write().clone()));

        // virtual_machine.compiler = Some(Arc::downgrade(&compiler));

        Self {
            virtual_machine,
            // compiler,
            modules: self.modules.clone(),
            #[cfg(feature = "dylibs")]
            dylibs: self.dylibs.clone(),
            id: EngineId::new(),
        }
    }
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

// Pre-parsed ASTs along with the global state to set before we start any further processing
// #[derive(Serialize, Deserialize)]
// struct BootstrapImage {
//     interner: Arc<ThreadedRodeo<lasso::Spur, FxBuildHasher>>,
//     syntax_object_id: usize,
//     sources: Sources,
//     programs: Vec<Vec<ExprKind>>,
// }

// Pre compiled programs along with the global state to set before we start any further processing
struct StartupBootstrapImage {
    syntax_object_id: usize,
    function_id: usize,
    sources: Sources,
    pre_kernel_programs: Vec<SerializableRawProgramWithSymbols>,
    post_kernel_programs: Vec<SerializableRawProgramWithSymbols>,
    kernel: Option<KernelImage>,
    compiler: Option<SerializableCompiler>,
}

struct KernelImage {
    // Kernel macros
    compiler: SerializableCompiler,
    sources: Sources,
    kernel_source: SerializableRawProgramWithSymbols,
}

#[derive(Serialize, Deserialize)]
pub struct NonInteractiveProgramImage {
    sources: Sources,
    program: SerializableRawProgramWithSymbols,
}

impl NonInteractiveProgramImage {
    pub fn write_bytes_to_file(&self, out: &Path) {
        let mut f = std::fs::File::create(out).unwrap();
        bincode::serialize_into(&mut f, self).unwrap();
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        bincode::serialize_into(&mut out, self).unwrap();
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        bincode::deserialize(bytes).unwrap()
    }
}

// fn steel_create_bootstrap() {
//     Engine::create_bootstrap_from_programs("src/boot/bootstrap.bin".into());
// }

pub struct LifetimeGuard<'a> {
    engine: &'a mut Engine,
    count: usize,
}

impl<'a> Drop for LifetimeGuard<'a> {
    fn drop(&mut self) {
        crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::free_n(self.count);
    }
}

impl<'a> LifetimeGuard<'a> {
    pub fn with_immutable_reference<
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        mut self,
        obj: &'a T,
    ) -> Self {
        assert_eq!(
            crate::gc::unsafe_erased_pointers::type_id::<T>(),
            core::any::TypeId::of::<EXT>()
        );

        crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::allocate_ro_object::<T, EXT>(
            obj,
        );
        self.count += 1;

        self
    }

    pub fn with_mut_reference<
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        mut self,
        obj: &'a mut T,
    ) -> Self {
        assert_eq!(
            crate::gc::unsafe_erased_pointers::type_id::<T>(),
            core::any::TypeId::of::<EXT>()
        );
        crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::allocate_rw_object::<T, EXT>(
            obj,
        );

        self.count += 1;

        self
    }

    pub fn consume<T>(self, mut thunk: impl FnMut(&mut Engine, Vec<SteelVal>) -> T) -> T {
        let values =
            crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::drain_weak_references_to_steelvals(self.count);

        thunk(self.engine, values)
    }

    pub fn consume_once<T>(self, mut thunk: impl FnOnce(&mut Engine, Vec<SteelVal>) -> T) -> T {
        let values =
            crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::drain_weak_references_to_steelvals(self.count);

        thunk(self.engine, values)
    }
}

impl RegisterValue for Engine {
    fn register_value_inner(&mut self, name: &str, value: SteelVal) -> &mut Self {
        let idx = self.virtual_machine.compiler.write().register(name);
        self.virtual_machine.insert_binding(idx, value);
        self
    }

    fn supply_context_arg(&mut self, ctx: &'static str, name: &'static str) -> &mut Self {
        if let Ok(existing) = self.extract_value(name) {
            if let SteelVal::BoxedFunction(f) = &existing {
                let func = generate_function(self, &SteelString::from(ctx), &existing, f);
                self.register_value(name, func);
            }
        }

        self
    }
}

#[steel_derive::function(name = "#%get-dylib")]
pub fn load_module_noop(target: &crate::rvals::SteelString) -> crate::rvals::Result<SteelVal> {
    stop!(Generic => "This engine has not been given the capability to load dylibs")
}

macro_rules! time {
    ($target:expr, $label:expr, $e:expr) => {{
        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        let e = $e;

        #[cfg(feature = "profiling")]
        log::debug!(target: $target, "{}: {:?}", $label, now.elapsed());

        e
    }};
}

static STATIC_DEFAULT_PRELUDE_MACROS: OnceCell<Arc<FxHashMap<InternedString, SteelMacro>>> =
    OnceCell::new();

static STATIC_DEFAULT_PRELUDE_MACROS_SANDBOX: OnceCell<Arc<FxHashMap<InternedString, SteelMacro>>> =
    OnceCell::new();

pub(crate) fn set_default_prelude_macros(
    prelude_macros: FxHashMap<InternedString, SteelMacro>,
    sandbox: bool,
) {
    if cfg!(feature = "sync") {
        if sandbox {
            STATIC_DEFAULT_PRELUDE_MACROS_SANDBOX
                .set(Arc::new(prelude_macros))
                .unwrap();
        } else {
            STATIC_DEFAULT_PRELUDE_MACROS
                .set(Arc::new(prelude_macros))
                .unwrap();
        }
    } else {
        DEFAULT_PRELUDE_MACROS.with(|x| {
            let mut guard = x.borrow_mut();
            *guard = Arc::new(prelude_macros);
        })
    }
}

pub(crate) fn default_prelude_macros() -> Arc<FxHashMap<InternedString, SteelMacro>> {
    if cfg!(feature = "sync") {
        STATIC_DEFAULT_PRELUDE_MACROS.get().cloned().unwrap_or(
            STATIC_DEFAULT_PRELUDE_MACROS_SANDBOX
                .get()
                .cloned()
                .unwrap_or_default(),
        )
    } else {
        DEFAULT_PRELUDE_MACROS.with(|x| x.borrow().clone())
    }
}

thread_local! {
    // TODO: Replace this with a once cell?
    pub(crate) static DEFAULT_PRELUDE_MACROS: RefCell<Arc<FxHashMap<InternedString, SteelMacro>>> = RefCell::new(Arc::new(HashMap::default()));
}

impl Engine {
    pub fn engine_id(&self) -> EngineId {
        self.virtual_machine.id
    }

    pub(crate) fn deep_clone(&self) -> Self {
        let mut engine = self.clone();
        engine.virtual_machine.global_env = engine.virtual_machine.global_env.deep_clone();

        engine.modules = self.modules.deep_clone();

        let mut compiler_copy = engine.virtual_machine.compiler.read().clone();
        compiler_copy.builtin_modules = engine.modules.clone();

        engine.virtual_machine.compiler = Arc::new(RwLock::new(compiler_copy));

        // Constants are literals, and their index hashes them, so they are not remapped.
        let constant_map = engine
            .virtual_machine
            .compiler
            .read()
            .constant_map
            .deep_clone();
        engine.virtual_machine.compiler.write().constant_map = constant_map;

        engine.virtual_machine.isolate_heap();
        engine
    }

    /// Function to access a kernel level execution environment
    /// Has access to primitives and syntax rules, but will not defer to a child
    /// kernel in the compiler
    pub(crate) fn new_kernel(sandbox: bool) -> Self {
        log::debug!(target:"kernel", "Instantiating a new kernel");
        #[cfg(feature = "profiling")]
        let mut total_time = crate::time::Instant::now();
        #[cfg(feature = "profiling")]
        let mut now = crate::time::Instant::now();
        let sources = Sources::new();
        let modules = ModuleContainer::with_expected_capacity();

        let compiler = Arc::new(RwLock::new(Compiler::default_without_kernel(
            sources,
            modules.clone(),
        )));

        let mut vm = Engine {
            virtual_machine: SteelThread::new(compiler),
            modules,
            #[cfg(feature = "dylibs")]
            dylibs: DylibContainers::new(),
            id: EngineId::new(),
        };

        time!(
            "engine-creation",
            "Registering builtin modules",
            register_builtin_modules(&mut vm, sandbox)
        );

        time!(
            "engine-creation",
            "Loading the ALL_MODULES prelude code",
            vm.compile_and_run_raw_program(crate::steel_vm::primitives::ALL_MODULES)
                .expect("loading ALL_MODULES failed")
        );

        // log::debug!(target: "kernel", "Registered modules in the kernel!: {:?}", now.elapsed());

        #[cfg(feature = "profiling")]
        let mut now = crate::time::Instant::now();

        let core_libraries = [crate::stdlib::PRELUDE];

        for core in core_libraries.into_iter() {
            if let Err(e) = vm.compile_and_run_raw_program(core) {
                vm.raise_error(e);
                panic!("Loading the standard library failed");
            }
        }

        // Initialize the global macro environment with the default one. This way
        // values won't leak when top level macros are defined - and modules can clone from
        // this to begin seeding their environment.

        set_default_prelude_macros(vm.in_scope_macros().clone(), sandbox);

        #[cfg(feature = "profiling")]
        log::debug!(target: "kernel", "Loaded prelude in the kernel!: {:?}", now.elapsed());

        #[cfg(feature = "profiling")]
        log::debug!(target: "pipeline_time", "Total kernel loading time: {:?}", total_time.elapsed());

        vm
    }

    /// Registers a source module resolvers. This differs from `register_module_resolver` which deals
    /// specifically with builtin modules, e.g. `BuiltInModule`. This will allow you to embed
    /// source modules that can be referenced via `(require ...)` at the scheme level.
    ///
    /// This is a more flexible version of the api provided by `register_steel_module`, which allows
    /// you to directly register a module with the name, and the associated text for that module.
    pub fn register_source_module_resolver<T: SourceModuleResolver + 'static>(
        &mut self,
        resolver: T,
    ) {
        self.virtual_machine
            .compiler
            .write()
            .register_source_module_resolver(resolver);
    }

    /// Register a module resolver. This is used for creating references to modules
    /// that don't exist within the compiler. Without this, you wouldn't be able to
    /// pre-compile or analyze code that is run within another host application, without
    /// exposing some kind of compiler from that hosts runtime. The requirement then
    /// is to expose some kind of module artifact that we can then consume.
    pub fn register_module_resolver<T: ModuleResolver + 'static>(&mut self, resolver: T) {
        for name in resolver.names() {
            // If the resolver can hand us the module now, bind the real value so that
            // `(require-builtin <name>)` can actually be _run_ by this engine, and not just
            // compiled against. If it can't be resolved, we still reserve the binding with
            // a void value so that the module can be referenced during compilation.
            let value = resolver
                .resolve(&name)
                .and_then(|module| module.into_steelval().ok())
                .unwrap_or(SteelVal::Void);

            self.register_value(&format!("%-builtin-module-{}", name), value);
        }

        self.modules.with_resolver(resolver);
    }

    pub fn builtin_modules(&self) -> &ModuleContainer {
        &self.modules
    }

    #[doc(hidden)]
    pub fn disallow_dylib_loading(&mut self) -> &mut Self {
        let mut module = self.modules.inner_mut();

        // TODO: This should actually just clone the whole module, and then add this definition
        // in. That way it has its own unique module loader.
        if let Some(builtin_module) = module.get_mut("steel/meta") {
            builtin_module.register_native_fn_definition(LOAD_MODULE_NOOP_DEFINITION);
        }

        drop(module);

        self
    }

    /// Function to access a kernel level execution environment
    /// Has access to primitives and syntax rules, but will not defer to a child
    /// kernel in the compiler
    pub(crate) fn new_bootstrap_kernel(sandbox: bool) -> Self {
        // If the interner has already been initialized, it most likely means that either:
        // 1) Tests are being run
        // 2) The parser was used in a standalone fashion, somewhere, which invalidates the bootstrap
        //    process
        //
        // There are a few solutions to this - one would probably be to not use a static interner,
        // however given that its a huge chore to pass around the interner everywhere there are strings,
        // its probably inevitable we have that.
        if get_interner().is_some() {
            return Engine::new_kernel(sandbox);
        }

        intern_modules();

        if matches!(option_env!("STEEL_BOOTSTRAP"), Some("false") | None) {
            let mut vm = Engine::new_kernel(sandbox);

            // let sources = vm.sources.clone();

            // vm.register_fn("report-error!", move |error: SteelErr| {
            //     raise_error(&sources, error);
            // });

            return vm;
        }

        log::debug!(target:"kernel", "Instantiating a new kernel");

        // let sources = Sources::new();
        // let modules = ModuleContainer::default();

        // let compiler = Arc::new(RwLock::new(Compiler::default_without_kernel(
        //     sources.clone(),
        //     modules.clone(),
        // )));

        // // TODO: Pass compiler down if we want eval!
        // let mut vm = Engine {
        //     virtual_machine: SteelThread::new(sources.clone(), compiler),
        //     modules,
        //     sources,
        //     #[cfg(feature = "dylibs")]
        //     dylibs: DylibContainers::new(),
        //     id: EngineId::new(),
        // };

        // if let Some(programs) = Engine::load_from_bootstrap(&mut vm) {
        //     register_builtin_modules(&mut vm, sandbox);

        //     for program in programs {
        //         vm.compiler.write().constant_map = program.constant_map.clone();
        //         vm.virtual_machine.constant_map = program.constant_map.clone();

        //         vm.run_raw_program(program).unwrap();
        //     }

        //     log::debug!(target: "kernel", "Loaded prelude in the kernel!");

        //     let sources = vm.sources.clone();

        //     vm.register_fn("report-error!", move |error: SteelErr| {
        //         raise_error(&sources, error);
        //     });

        //     vm
        // } else {
        let mut vm = Engine::new_kernel(sandbox);

        // let sources = vm.sources.clone();

        // vm.register_fn("report-error!", move |error: SteelErr| {
        //     raise_error(&sources, error);
        // });

        vm
        // }
    }

    // fn load_from_bootstrap(vm: &mut Engine) -> Option<Vec<RawProgramWithSymbols>> {
    //     if matches!(option_env!("STEEL_BOOTSTRAP"), Some("false") | None) {
    //         return None;
    //     } else {
    //         println!("LOADING A KERNEL FROM THE BIN FILE");
    //     }

    //     let bootstrap: StartupBootstrapImage =
    //         bincode::deserialize(KERNEL_BIN_FILE.with(|x| x.get())?).unwrap();

    //     // Set the syntax object id to be AFTER the previous items have been parsed
    //     SYNTAX_OBJECT_ID.store(
    //         bootstrap.syntax_object_id,
    //         std::sync::atomic::Ordering::Relaxed,
    //     );

    //     crate::compiler::code_gen::FUNCTION_ID
    //         .store(bootstrap.function_id, std::sync::atomic::Ordering::Relaxed);

    //     vm.sources = bootstrap.sources;
    //     // vm.compiler.macro_env = bootstrap.macros;

    //     todo!();

    //     Some(
    //         bootstrap
    //             .pre_kernel_programs
    //             .into_iter()
    //             .map(SerializableRawProgramWithSymbols::into_raw_program)
    //             .collect(),
    //     )
    // }

    /// Creates a statically linked program ready to deserialize
    pub fn create_non_interactive_program_image<E: AsRef<str> + Into<Cow<'static, str>>>(
        expr: E,
        path: PathBuf,
    ) -> Result<NonInteractiveProgramImage> {
        let mut engine = Engine::new();

        engine
            .emit_raw_program(expr, path)?
            .into_serializable_program()
            .map(|program| NonInteractiveProgramImage {
                sources: engine.virtual_machine.compiler.read().sources.clone(),
                program,
            })
    }

    // Execute from a statically linked non interactive program
    pub fn execute_non_interactive_program_image(program: &'static [u8]) -> Result<()> {
        // This _has_ to match the as the creation of the program above.
        // So, engine first, then non interactive program.
        let mut engine = Engine::new();
        let program = crate::steel_vm::engine::NonInteractiveProgramImage::from_bytes(program);

        engine.virtual_machine.compiler.write().sources = program.sources;

        // TODO: The constant map needs to be brought back as well. Install it here.
        // it needs to get installed in the VM and the compiler. Lets just try that now.

        let raw_program = SerializableRawProgramWithSymbols::into_raw_program(program.program);

        engine.virtual_machine.constant_map = raw_program.constant_map.clone();
        engine.virtual_machine.compiler.write().constant_map = raw_program.constant_map.clone();

        let results = engine.run_raw_program(raw_program);

        if let Err(e) = results {
            raise_error(&engine.virtual_machine.compiler.read().sources, e);
        }

        Ok(())
    }

    // Create kernel bootstrap
    // pub fn create_kernel_bootstrap_from_programs(output_path: PathBuf) {
    //     let sources = Sources::new();

    //     let mut vm = Engine {
    //         virtual_machine: SteelThread::new(sources.clone()),
    //         compiler: Arc::new(RwLock::new(Compiler::default())),
    //         constants: None,
    //         modules: ModuleContainer::default(),
    //         sources,
    //         #[cfg(feature = "dylibs")]
    //         dylibs: DylibContainers::new(),
    //         id: EngineId::new(),
    //     };

    //     register_builtin_modules(&mut vm, false);

    //     let mut programs = Vec::new();

    //     let bootstrap_sources = [
    //         crate::steel_vm::primitives::ALL_MODULES,
    //         crate::stdlib::PRELUDE,
    //     ];

    //     for source in bootstrap_sources {
    //         let raw_program = vm.emit_raw_program_no_path(source).unwrap();
    //         programs.push(raw_program.clone());
    //         vm.run_raw_program(raw_program).unwrap();
    //     }

    //     // Grab the last value of the offset
    //     let syntax_object_id = SYNTAX_OBJECT_ID.load(std::sync::atomic::Ordering::Relaxed);
    //     let function_id =
    //         crate::compiler::code_gen::FUNCTION_ID.load(std::sync::atomic::Ordering::Relaxed);

    //     let bootstrap = StartupBootstrapImage {
    //         syntax_object_id,
    //         function_id,
    //         sources: vm.sources,
    //         pre_kernel_programs: programs
    //             .into_iter()
    //             .map(RawProgramWithSymbols::into_serializable_program)
    //             .collect::<Result<_>>()
    //             .unwrap(),
    //         // macros: vm.compiler.macro_env,
    //         post_kernel_programs: Vec::new(),
    //         kernel: None,
    //         compiler: None,
    //     };

    //     // Encode to something implementing `Write`
    //     let mut f = std::fs::File::create(output_path).unwrap();
    //     bincode::serialize_into(&mut f, &bootstrap).unwrap();
    // }

    // pub fn create_new_engine_from_bootstrap(output_path: PathBuf) {
    //     let sources = Sources::new();
    //     let mut vm = Engine {
    //         virtual_machine: SteelThread::new(sources.clone()),
    //         compiler: Arc::new(RwLock::new(Compiler::default())),
    //         constants: None,
    //         modules: ModuleContainer::default(),
    //         sources,
    //         #[cfg(feature = "dylibs")]
    //         dylibs: DylibContainers::new(),
    //         id: EngineId::new(),
    //     };

    //     register_builtin_modules(&mut vm, false);

    //     let mut pre_kernel_programs = Vec::new();

    //     let bootstrap_sources = [
    //         crate::steel_vm::primitives::ALL_MODULES,
    //         crate::stdlib::PRELUDE,
    //     ];

    //     for source in bootstrap_sources {
    //         let raw_program = vm.emit_raw_program_no_path(source).unwrap();
    //         pre_kernel_programs.push(raw_program.clone());
    //         vm.run_raw_program(raw_program).unwrap();
    //     }

    //     // This will be our new top level engine
    //     let mut top_level_engine = vm.clone();

    //     let sources = vm.sources.clone();

    //     vm.register_fn("report-error!", move |error: SteelErr| {
    //         raise_error(&sources, error);
    //     });

    //     let (kernel, kernel_program) = Kernel::bootstrap(vm);

    //     // Create kernel for the compiler for the top level vm
    //     top_level_engine.compiler.write().kernel = Some(kernel);

    //     let builtin_modules =
    //         ["(require \"#%private/steel/contract\" (for-syntax \"#%private/steel/contract\"))"];

    //     let mut post_kernel_programs = Vec::new();

    //     for source in builtin_modules {
    //         let raw_program = top_level_engine.emit_raw_program_no_path(source).unwrap();
    //         post_kernel_programs.push(raw_program.clone());
    //         top_level_engine.run_raw_program(raw_program).unwrap();
    //     }

    //     // Grab the last value of the offset
    //     let syntax_object_id = SYNTAX_OBJECT_ID.load(std::sync::atomic::Ordering::Relaxed);
    //     let function_id =
    //         crate::compiler::code_gen::FUNCTION_ID.load(std::sync::atomic::Ordering::Relaxed);

    //     let kernel_sources = top_level_engine
    //         .compiler
    //         .write()
    //         .kernel
    //         .as_ref()
    //         .unwrap()
    //         .engine
    //         .sources
    //         .clone();
    //     let bootstrap = StartupBootstrapImage {
    //         syntax_object_id,
    //         function_id,
    //         sources: top_level_engine.sources,
    //         pre_kernel_programs: pre_kernel_programs
    //             .into_iter()
    //             .map(RawProgramWithSymbols::into_serializable_program)
    //             .collect::<Result<_>>()
    //             .unwrap(),
    //         post_kernel_programs: post_kernel_programs
    //             .into_iter()
    //             .map(RawProgramWithSymbols::into_serializable_program)
    //             .collect::<Result<_>>()
    //             .unwrap(),
    //         kernel: Some(KernelImage {
    //             compiler: top_level_engine
    //                 .compiler
    //                 .write()
    //                 .kernel
    //                 .take()
    //                 .unwrap()
    //                 .engine
    //                 .compiler
    //                 .write()
    //                 .into_serializable_compiler()
    //                 .unwrap(),
    //             sources: kernel_sources,
    //             kernel_source: kernel_program.into_serializable_program().unwrap(),
    //         }),
    //         compiler: Some(
    //             top_level_engine
    //                 .compiler
    //                 .write()
    //                 .into_serializable_compiler()
    //                 .unwrap(),
    //         ),
    //     };

    //     // Encode to something implementing `Write`
    //     let mut f = std::fs::File::create(output_path).unwrap();
    //     bincode::serialize_into(&mut f, &bootstrap).unwrap();
    // }

    // pub fn top_level_load_from_bootstrap(bin: &[u8]) -> Engine {
    //     let bootstrap: StartupBootstrapImage = bincode::deserialize(bin).unwrap();

    //     let sources = Sources::new();
    //     // This is going to be the kernel
    //     let mut vm = Engine {
    //         virtual_machine: SteelThread::new(sources.clone()),
    //         compiler: Arc::new(RwLock::new(Compiler::default())),
    //         constants: None,
    //         modules: ModuleContainer::default(),
    //         sources,
    //         #[cfg(feature = "dylibs")]
    //         dylibs: DylibContainers::new(),
    //         id: EngineId::new(),
    //     };

    //     // Register the modules
    //     register_builtin_modules(&mut vm, false);

    //     // Set the syntax object id to be AFTER the previous items have been parsed
    //     SYNTAX_OBJECT_ID.store(
    //         bootstrap.syntax_object_id,
    //         std::sync::atomic::Ordering::Relaxed,
    //     );

    //     crate::compiler::code_gen::FUNCTION_ID
    //         .store(bootstrap.function_id, std::sync::atomic::Ordering::Relaxed);

    //     let bootstrap_kernel = bootstrap.kernel.unwrap();

    //     vm.sources = bootstrap_kernel.sources;
    //     vm.compiler = Arc::new(RwLock::new(bootstrap_kernel.compiler.into_compiler()));

    //     // TODO: Only need to bring around the last constant map
    //     for program in bootstrap
    //         .pre_kernel_programs
    //         .into_iter()
    //         .map(SerializableRawProgramWithSymbols::into_raw_program)
    //     {
    //         vm.compiler.write().constant_map = program.constant_map.clone();
    //         vm.virtual_machine.constant_map = program.constant_map.clone();

    //         vm.run_raw_program(program).unwrap();
    //     }

    //     log::debug!(target: "kernel", "Loaded prelude in the kernel!");

    //     let sources = vm.sources.clone();

    //     vm.register_fn("report-error!", move |error: SteelErr| {
    //         raise_error(&sources, error);
    //     });

    //     // Now we're going to set up the top level environment
    //     let mut kernel = Kernel::initialize_post_bootstrap(vm.clone());

    //     kernel
    //         .engine
    //         .run_raw_program(bootstrap_kernel.kernel_source.into_raw_program())
    //         .unwrap();

    //     vm.sources = bootstrap.sources;
    //     vm.compiler = Arc::new(RwLock::new(bootstrap.compiler.unwrap().into_compiler()));
    //     vm.compiler.write().kernel = Some(kernel);

    //     for program in bootstrap
    //         .post_kernel_programs
    //         .into_iter()
    //         .map(SerializableRawProgramWithSymbols::into_raw_program)
    //     {
    //         vm.compiler.write().constant_map = program.constant_map.clone();
    //         vm.virtual_machine.constant_map = program.constant_map.clone();

    //         vm.run_raw_program(program).unwrap();
    //     }

    //     vm
    // }

    // fn create_bootstrap() {
    //     let sources = Sources::new();

    //     let mut vm = Engine {
    //         virtual_machine: SteelThread::new(sources.clone()),
    //         compiler: Arc::new(RwLock::new(Compiler::default())),
    //         constants: None,
    //         modules: ModuleContainer::default(),
    //         sources,
    //         #[cfg(feature = "dylibs")]
    //         dylibs: DylibContainers::new(),
    //         id: EngineId::new(),
    //     };

    //     register_builtin_modules(&mut vm, false);

    //     let mut asts = Vec::new();

    //     let bootstrap_sources = [
    //         crate::steel_vm::primitives::ALL_MODULES,
    //         crate::stdlib::PRELUDE,
    //     ];

    //     for source in bootstrap_sources {
    //         let id = vm.sources.add_source(source.to_string(), None);

    //         // Could fail here
    //         let parsed: Vec<ExprKind> = Parser::new(source, Some(id))
    //             .collect::<core::result::Result<_, _>>()
    //             .unwrap();

    //         asts.push(parsed.clone());

    //         vm.run_raw_program_from_exprs(parsed).unwrap();
    //     }

    //     // Grab the last value of the offset
    //     let syntax_object_id = SYNTAX_OBJECT_ID.load(std::sync::atomic::Ordering::Relaxed);

    //     let bootstrap = BootstrapImage {
    //         interner: take_interner(),
    //         syntax_object_id,
    //         sources: vm.sources,
    //         programs: asts,
    //     };

    //     // Encode to something implementing `Write`
    //     let mut f = std::fs::File::create("src/boot/bootstrap.bin").unwrap();
    //     bincode::serialize_into(&mut f, &bootstrap).unwrap();
    // }

    /// Instantiates a raw engine instance. Includes no primitives or prelude.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new_raw();
    /// assert!(vm.run("(+ 1 2 3").is_err()); // + is a free identifier
    /// ```
    pub fn new_raw() -> Self {
        #[cfg(all(feature = "sync", feature = "biased", not(feature = "triomphe")))]
        {
            steel_rc::register_thread();
        }

        let sources = Sources::new();
        let modules = ModuleContainer::default();

        let compiler = Arc::new(RwLock::new(Compiler::default_with_kernel(
            sources,
            modules.clone(),
        )));

        Engine {
            virtual_machine: SteelThread::new(compiler),
            modules,
            #[cfg(feature = "dylibs")]
            dylibs: DylibContainers::new(),
            id: EngineId::new(),
        }
    }

    pub fn set_prelude_string(&mut self, prelude_string: Cow<'static, str>) {
        self.virtual_machine
            .compiler
            .write()
            .module_manager
            .set_prelude_string(prelude_string);
    }

    pub fn with_default_prelude_string(&mut self) {
        self.virtual_machine
            .compiler
            .write()
            .module_manager
            .use_default_prelude_string();
    }

    /// Instantiates a raw engine instance. Includes no primitives or prelude, and does not
    /// allow for kernel level macro expansion.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new_raw_no_kernel();
    /// assert!(vm.run("(+ 1 2 3").is_err()); // + is a free identifier
    /// ```
    pub fn new_raw_no_kernel() -> Self {
        #[cfg(all(feature = "sync", feature = "biased", not(feature = "triomphe")))]
        {
            steel_rc::register_thread();
        }

        let sources = Sources::new();
        let modules = ModuleContainer::default();

        let compiler = Arc::new(RwLock::new(Compiler::default_without_kernel(
            sources,
            modules.clone(),
        )));

        let mut engine = Engine {
            virtual_machine: SteelThread::new(compiler),
            modules,
            #[cfg(feature = "dylibs")]
            dylibs: DylibContainers::new(),
            id: EngineId::new(),
        };

        bootstrap_globals(&mut engine);
        engine.register_value(
            "#%immutable-struct-type",
            SteelVal::FuncV(crate::values::structs::make_immutable_struct_type),
        );
        engine.register_value(
            "#%values-destructure",
            SteelVal::FuncV(crate::primitives::lists::steel_destructure_values),
        );
        engine.register_value(
            "#%values-ref",
            SteelVal::FuncV(crate::primitives::lists::steel_list_ref),
        );

        // Set the prelude string to be completely empty,
        // so we'll have to get that working yet.
        engine.set_prelude_string(Cow::Borrowed(""));

        engine
    }

    pub fn report_engine_stats(&self) -> EngineStatistics {
        EngineStatistics {
            rooted_count: self.globals().len(),
            constants_count: self.virtual_machine.compiler.read().constant_map.len(),
            sources_size: self.virtual_machine.compiler.read().sources.size_in_bytes(),
        }
    }

    /// Registers a steel module. This is a more streamlined version of the
    /// api provided by `register_source_module_resolver`.
    pub fn register_steel_module(&mut self, module_name: String, text: String) {
        self.virtual_machine
            .compiler
            .write()
            .register_builtin(module_name, text);
    }

    /// Instantiates a new engine instance with all primitive functions enabled.
    /// This excludes the prelude and contract files.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new_base();
    /// // map is found in the prelude, so this will fail
    /// assert!(vm.run(r#"(map (lambda (x) 10) (list 1 2 3 4 5))"#).is_err());
    /// ```
    #[inline]
    pub fn new_base() -> Self {
        let mut vm = Engine::new_raw();
        // Embed any primitives that we want to use
        register_builtin_modules(&mut vm, false);

        vm.compile_and_run_raw_program(crate::steel_vm::primitives::ALL_MODULES)
            .unwrap();

        vm
    }

    // pub fn cache_modules(&mut self) {
    //     self.virtual_machine
    //         .compiler
    //         .write()
    //         .module_manager
    //         .compiled_modules
    //         .cache_modules();
    // }

    /// Turn contracts on in the VM
    pub fn with_contracts(&mut self, contracts: bool) -> &mut Self {
        self.virtual_machine.with_contracts(contracts);
        self
    }

    #[inline]
    pub fn new_sandboxed() -> Self {
        let mut engine = fresh_kernel_image(true);

        engine.virtual_machine.compiler.write().kernel = Some(Kernel::new());

        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        if let Err(e) = engine.run(PRELUDE_WITHOUT_BASE) {
            raise_error(&engine.virtual_machine.compiler.read().sources, e);
            panic!("This shouldn't happen!");
        }

        #[cfg(feature = "profiling")]
        log::info!(target: "engine-creation", "Engine Creation: {:?}", now.elapsed());

        // Block dylib loading for sandboxed instances
        engine.disallow_dylib_loading();

        engine
    }

    /// Call the print method within the VM
    pub fn call_printing_method_in_context(&mut self, argument: SteelVal) -> Result<SteelVal> {
        let function = self.extract_value("displayln")?;
        self.call_function_with_args(function, vec![argument])
    }

    /// Internal API for calling a function directly
    pub fn call_function_with_args(
        &mut self,
        function: SteelVal,
        arguments: Vec<SteelVal>,
    ) -> Result<SteelVal> {
        let constant_map = self.virtual_machine.compiler.read().constant_map.clone();

        self.virtual_machine
            .call_function(constant_map, function, arguments)
    }

    pub fn call_function_with_args_from_mut_slice(
        &mut self,
        function: SteelVal,
        arguments: &mut [SteelVal],
    ) -> Result<SteelVal> {
        let constant_map = self.virtual_machine.compiler.read().constant_map.clone();

        self.virtual_machine
            .call_function_from_mut_slice(constant_map, function, arguments)
    }

    /// Call a function by name directly within the target environment
    pub fn call_function_by_name_with_args(
        &mut self,
        function: &str,
        arguments: Vec<SteelVal>,
    ) -> Result<SteelVal> {
        let constant_map = self.virtual_machine.compiler.read().constant_map.clone();
        self.extract_value(function).and_then(|function| {
            self.virtual_machine
                .call_function(constant_map, function, arguments)
        })
    }

    pub fn call_function_by_name_with_args_from_mut_slice(
        &mut self,
        function: &str,
        arguments: &mut [SteelVal],
    ) -> Result<SteelVal> {
        let constant_map = self.virtual_machine.compiler.read().constant_map.clone();

        self.extract_value(function).and_then(|function| {
            self.virtual_machine
                .call_function_from_mut_slice(constant_map, function, arguments)
        })
    }

    /// Nothing fancy, just run it
    pub fn run<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        input: E,
    ) -> Result<Vec<SteelVal>> {
        self.compile_and_run_raw_program(input)
    }

    pub fn with_immutable_reference<
        'a,
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        &'a mut self,
        obj: &'a T,
    ) -> LifetimeGuard<'a> {
        assert_eq!(
            crate::gc::unsafe_erased_pointers::type_id::<T>(),
            core::any::TypeId::of::<EXT>()
        );

        crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::allocate_ro_object::<T, EXT>(
            obj,
        );

        LifetimeGuard {
            engine: self,
            count: 1,
        }
    }

    pub fn with_mut_reference<
        'a,
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        &'a mut self,
        obj: &'a mut T,
    ) -> LifetimeGuard<'a> {
        assert_eq!(
            crate::gc::unsafe_erased_pointers::type_id::<T>(),
            core::any::TypeId::of::<EXT>()
        );

        crate::gc::unsafe_erased_pointers::OpaqueReferenceNursery::allocate_rw_object::<T, EXT>(
            obj,
        );

        LifetimeGuard {
            engine: self,
            count: 1,
        }
    }

    // Tie the lifetime of this object to the scope of this execution
    pub fn run_with_reference<
        'a,
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        &'a mut self,
        obj: &'a mut T,
        bind_to: &'a str,
        script: &'a str,
    ) -> Result<SteelVal> {
        self.with_mut_reference(obj).consume(move |engine, args| {
            let mut args = args.into_iter();

            engine.update_value(bind_to, args.next().unwrap());

            let res = engine.compile_and_run_raw_program(Cow::Owned(script.to_owned()));

            engine.update_value(bind_to, SteelVal::Void);

            res.map(|x| x.into_iter().next().unwrap_or(SteelVal::Void))
        })
    }

    pub fn run_with_reference_from_path<
        'a,
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        &'a mut self,
        obj: &'a mut T,
        bind_to: &'a str,
        script: &'a str,
        path: PathBuf,
    ) -> Result<SteelVal> {
        self.with_mut_reference(obj).consume(move |engine, args| {
            let mut args = args.into_iter();

            engine.update_value(bind_to, args.next().unwrap());

            let res = engine
                .compile_and_run_raw_program_with_path(Cow::Owned(script.to_owned()), path.clone());

            engine.update_value(bind_to, SteelVal::Void);

            res.map(|x| x.into_iter().next().unwrap_or(SteelVal::Void))
        })
    }

    pub fn run_thunk_with_reference<
        'a,
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        &'a mut self,
        obj: &'a mut T,
        mut thunk: impl FnMut(&mut Engine, SteelVal) -> Result<SteelVal>,
    ) -> Result<SteelVal> {
        self.with_mut_reference(obj).consume(|engine, args| {
            let mut args = args.into_iter();

            thunk(engine, args.next().unwrap_or(SteelVal::Void))
        })
    }

    pub fn run_thunk_with_ro_reference<
        'a,
        'b: 'a,
        T: CustomReference + ReferenceMarker<'b, Static = EXT> + 'b,
        EXT: CustomReference + 'static,
    >(
        &'a mut self,
        obj: &'a T,
        mut thunk: impl FnMut(&mut Engine, SteelVal) -> Result<SteelVal>,
    ) -> Result<SteelVal> {
        self.with_immutable_reference(obj).consume(|engine, args| {
            let mut args = args.into_iter();

            thunk(engine, args.next().unwrap_or(SteelVal::Void))
        })
    }

    /// Instantiates a new engine instance with all the primitive functions enabled.
    /// This is the most general engine entry point, and includes both the contract and
    /// prelude files in the root.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new();
    /// vm.run(r#"(+ 1 2 3)"#).unwrap();
    /// ```
    pub fn new() -> Self {
        #[cfg(all(feature = "sync", feature = "biased", not(feature = "triomphe")))]
        {
            steel_rc::register_thread();
        }
        let mut engine = fresh_kernel_image(false);

        {
            engine.virtual_machine.compiler.write().kernel = Some(Kernel::new());
        }

        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        if let Err(e) = engine.run(PRELUDE_WITHOUT_BASE) {
            raise_error(&engine.virtual_machine.compiler.read().sources, e);
            panic!("This shouldn't happen!");
        }

        #[cfg(feature = "profiling")]
        log::info!(target: "engine-creation", "Engine Creation: {:?}", now.elapsed());

        engine
    }

    /// Adds a directory for the engine to resolve paths from.
    ///
    /// By default, the engine will search $STEEL_HOME/cogs for modules,
    /// but any additional path added this way will increase the module
    /// resolution search space.
    pub fn add_search_directory(&mut self, dir: PathBuf) {
        self.virtual_machine
            .compiler
            .write()
            .add_search_directory(dir)
    }

    pub fn with_interrupted(&mut self, interrupted: Arc<AtomicBool>) {
        self.virtual_machine.with_interrupted(interrupted);
    }

    pub fn get_thread_state_controller(&self) -> ThreadStateController {
        self.virtual_machine.synchronizer.state.clone()
    }

    /// Consumes the current `Engine` and emits a new `Engine` with the prelude added
    /// to the environment. The prelude won't work unless the primitives are also enabled.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new_base().with_prelude().unwrap();
    /// vm.run("(+ 1 2 3)").unwrap();
    /// ```
    pub fn with_prelude(mut self) -> Result<Self> {
        let core_libraries = &[crate::stdlib::PRELUDE];

        for core in core_libraries {
            self.compile_and_run_raw_program(*core)?;
        }

        Ok(self)
    }

    /// Registers the prelude to the environment of the given Engine.
    /// The prelude won't work unless the primitives are also enabled.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new_base();
    /// vm.register_prelude().unwrap();
    /// vm.run("(+ 1 2 3)").unwrap();
    /// ```
    pub fn register_prelude(&mut self) -> Result<&mut Self> {
        let core_libraries = &[crate::stdlib::PRELUDE];

        for core in core_libraries {
            self.compile_and_run_raw_program(*core)?;
        }

        Ok(self)
    }

    // Registers the given module into the virtual machine
    pub fn register_module(&mut self, module: BuiltInModule) -> &mut Self {
        {
            use crate::gc::ShareableMut;
            // Generating the wrappers waits for the heap at a safepoint, where a collection on
            // another thread can visit this module, so the module stays unlocked meanwhile.
            let mut context_functions = module.module.read().context_functions.clone();
            if !context_functions.is_empty() {
                let funcs = register_context_functions(self, &mut context_functions);
                let mut guard = module.module.write();
                // Overwrite the existing values, and then insert the module.
                for (key, func) in funcs {
                    guard.register_value(&key, func);
                }
            }
        }

        // Add the module to the map
        self.modules.insert(module.name(), module.clone());
        // Register the actual module itself as a value to make the virtual machine capable of reading from it
        self.register_value(
            module.unreadable_name().as_str(),
            module.into_steelval().unwrap(),
        );

        self
    }

    #[cfg(feature = "dylibs")]
    pub fn register_external_module(
        &mut self,
        module: abi_stable::std_types::RBox<FFIModule>,
    ) -> Result<&mut Self> {
        let external_module = FFIWrappedModule::new(module, None)?.build();

        self.modules
            .insert(external_module.name(), external_module.clone());

        self.register_value(
            external_module.unreadable_name().as_str(),
            external_module.into_steelval().unwrap(),
        );

        Ok(self)
    }

    pub fn emit_raw_program_no_path<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        expr: E,
    ) -> Result<RawProgramWithSymbols> {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .compile_executable(expr, None)
        })
    }

    pub fn emit_raw_program<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        expr: E,
        path: PathBuf,
    ) -> Result<RawProgramWithSymbols> {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .compile_executable(expr, Some(path))
        })
    }

    /// Give in-memory source a diagnostic name without granting a filesystem module origin.
    pub fn emit_raw_program_with_source_name<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        expr: E,
        source_name: PathBuf,
    ) -> Result<RawProgramWithSymbols> {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .compile_executable_with_source_name(expr, Some(source_name), None)
        })
    }

    #[doc(hidden)]
    pub fn debug_build_strings(&mut self, program: RawProgramWithSymbols) -> Result<Vec<String>> {
        program.debug_generate_instructions(&mut self.virtual_machine.compiler.write().symbol_map)
    }

    pub fn debug_print_build(
        &mut self,
        name: String,
        program: RawProgramWithSymbols,
    ) -> Result<()> {
        program.debug_build(name, &mut self.virtual_machine.compiler.write().symbol_map)
    }

    pub fn globals(&self) -> MappedRwLockReadGuard<'_, Vec<InternedString>> {
        RwLockReadGuard::map(self.virtual_machine.compiler.read(), |x| {
            x.symbol_map.values()
        })
    }

    // TODO: Remove duplicates!
    pub fn readable_globals(&self, after_offset: usize) -> Vec<InternedString> {
        let mut seen = HashSet::new();

        self.virtual_machine
            .compiler
            .read()
            .symbol_map
            .values()
            .iter()
            .skip(after_offset)
            .filter(|x| {
                let resolved = x.resolve();
                !resolved.starts_with("#")
                    && !resolved.starts_with("%")
                    && !resolved.starts_with("mangler#%")
                    && !resolved.starts_with(MANGLER_PREFIX)
                    && !resolved.starts_with("__module")
                    && !resolved.ends_with("__doc__")
            })
            .filter_map(|x| {
                if seen.contains(x) {
                    None
                } else {
                    seen.insert(x);
                    Some(x)
                }
            })
            .copied()
            .collect()
    }

    // Generate dynamically linked files, containing all of the necessary information
    // This means - compiling all macros as well.
    fn load_raw_program(&mut self, mut program: RawProgramWithSymbols) {
        fn eval_atom(t: &SyntaxObject) -> Result<SteelVal> {
            match &t.ty {
                TokenType::BooleanLiteral(b) => Ok((*b).into()),
                TokenType::Number(n) => n.resolve().into_steelval(),
                TokenType::StringLiteral(s) => Ok(SteelVal::StringV(s.clone().into())),
                TokenType::CharacterLiteral(c) => Ok(SteelVal::CharV(*c)),
                // TODO: Keywords shouldn't be misused as an expression - only in function calls are keywords allowed
                TokenType::Keyword(k) => Ok(SteelVal::SymbolV((*k).into())),
                what => {
                    // println!("getting here in the eval_atom - code_gen");
                    stop!(UnexpectedToken => what; t.span)
                }
            }
        }

        for expr in &mut program.instructions {
            // Reform the program to conform to the current state of _this_ engine.
            for instruction in expr.iter_mut() {
                todo!()

                // match instruction {
                //     Instruction {
                //         op_code: OpCode::PUSHCONST,
                //         contents: Some(Expr::Atom(constant_value)),
                //         ..
                //     } => {
                //         let value =
                //             eval_atom(&constant_value).expect("This must be a constant value");

                //         instruction.payload_size = self.compiler.constant_map.add_or_get(value);
                //     }

                //     Instruction {
                //         op_code: OpCode::PUSHCONST,
                //         contents: Some(Expr::List(expression)),
                //         ..
                //     } => {
                //         let value = SteelVal::try_from(expression.clone())
                //             .expect("This conversion must work");

                //         instruction.payload_size = self.compiler.constant_map.add_or_get(value);
                //     }

                //     _ => {
                //         todo!()
                //     }
                // }
            }
        }
    }

    pub fn expand_to_file<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        exprs: E,
        path: PathBuf,
    ) {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .fully_expand_to_file(exprs, Some(path))
                .unwrap()
        });
    }

    pub fn load_from_expanded_file(&mut self, path: &str) {
        let program = self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .load_from_file(path)
                .unwrap()
        });

        self.run_raw_program(program).unwrap();
    }

    // TODO -> clean up this API a lot
    pub fn compile_and_run_raw_program_with_path<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        exprs: E,
        path: PathBuf,
    ) -> Result<Vec<SteelVal>> {
        let program = self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .compile_executable(exprs, Some(path))
        })?;

        self.run_raw_program(program)
    }

    pub(crate) fn run_raw_program_from_exprs(
        &mut self,
        exprs: Vec<ExprKind>,
    ) -> Result<Vec<SteelVal>> {
        let program = self
            .virtual_machine
            .compiler
            .write()
            .compile_executable_from_expressions(exprs)?;
        self.run_raw_program(program)
    }

    pub fn compile_and_run_raw_program<E: AsRef<str> + Into<Cow<'static, str>>>(
        &mut self,
        exprs: E,
    ) -> Result<Vec<SteelVal>> {
        #[cfg(feature = "biased")]
        QueueHandle::register_thread();

        let program = self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .compile_executable(exprs, None)
        })?;

        self.run_raw_program(program)
    }

    pub fn raw_program_to_executable(
        &mut self,
        program: RawProgramWithSymbols,
    ) -> Result<Executable> {
        let symbol_map_offset = self.virtual_machine.compiler.read().symbol_map.len();

        let result = program.build(
            "TestProgram".to_string(),
            &mut self.virtual_machine.compiler.write().symbol_map,
        );

        // Revisit if we need to do this at all?
        if result.is_err() {
            let mut guard = self.virtual_machine.compiler.write();

            // Reset the compiled modules as well.
            guard.symbol_map.roll_back(symbol_map_offset);
            guard.module_manager.rollback_metadata();
        }

        result
    }

    // TODO: Add doc for this
    #[doc(hidden)]
    pub fn environment_offset(&self) -> GlobalCheckpoint {
        GlobalCheckpoint {
            symbol_map_offset: self.virtual_machine.compiler.read().symbol_map.len(),
            globals_offset: self.virtual_machine.global_env.len(),
        }
    }

    // TODO: Add doc for this
    #[doc(hidden)]
    pub fn rollback_to_checkpoint(&mut self, checkpoint: GlobalCheckpoint) -> Result<()> {
        self.virtual_machine
            .compiler
            .write()
            .symbol_map
            .roll_back(checkpoint.symbol_map_offset);

        // // TODO: Does this even need to happen?
        // #[cfg(feature = "sync")]
        // {
        //     self.virtual_machine
        //         .global_env
        //         .bindings_vec
        //         .write()
        //         // .unwrap()
        //         .truncate(checkpoint.globals_offset);
        // }

        #[cfg(not(feature = "sync"))]
        {
            self.virtual_machine
                .global_env
                .bindings_vec
                .truncate(checkpoint.globals_offset);
        }

        Ok(())
    }

    pub fn run_raw_program(&mut self, program: RawProgramWithSymbols) -> Result<Vec<SteelVal>> {
        // TODO: Add hook here to check what values are now unreachable!
        let executable = self.raw_program_to_executable(program)?;

        self.gc_shadowed_roots();

        self.virtual_machine.run_executable(&executable)
    }

    fn gc_shadowed_roots(&mut self) {
        // Unfortunately, we have to invoke a whole GC algorithm here
        // for shadowed rooted values
        let guard = self.virtual_machine.compiler.write();
        if guard.symbol_map.free_list.should_collect() {
            drop(guard);

            self.virtual_machine.with_heap(None, |thread, heap| {
                #[cfg(feature = "sync")]
                thread.with_locked_env(|ctx, env| {
                    let released = {
                        let mut compiler = ctx.compiler.write();
                        let compiler = &mut *compiler;
                        GlobalSlotRecycler::free_shadowed_rooted_values(
                            // &mut self.virtual_machine.global_env.bindings_vec.write(),
                            env.0.as_mut_slice(),
                            // .unwrap(),
                            &mut compiler.symbol_map,
                            &compiler.function_ids,
                            heap,
                        )
                    };
                    // Released by `with_heap` once the heap and environment are unlocked.
                    heap.released.extend(released);

                    // TODO:
                    // It is also necessary to keep track of the values to drop
                    // for closures - this can be done by tracking the closure id
                    // throughout the generated bytecode. Same way we keep track of
                    // the referenced globals; we track the referenced closures.
                    // FIXME: Add that code here

                    ctx.compiler
                        .write()
                        .symbol_map
                        .free_list
                        .increment_generation();
                });

                #[cfg(not(feature = "sync"))]
                thread.with_locked_env(|ctx| {
                    let released = {
                        let mut compiler = ctx.compiler.write();
                        let compiler = &mut *compiler;
                        GlobalSlotRecycler::free_shadowed_rooted_values(
                            &mut ctx.global_env.bindings_vec,
                            &mut compiler.symbol_map,
                            &compiler.function_ids,
                            heap,
                        )
                    };
                    // Released by `with_heap` once the heap is unlocked.
                    heap.released.extend(released);

                    // TODO:
                    // It is also necessary to keep track of the values to drop
                    // for closures - this can be done by tracking the closure id
                    // throughout the generated bytecode. Same way we keep track of
                    // the referenced globals; we track the referenced closures.
                    // FIXME: Add that code here

                    ctx.compiler
                        .write()
                        .symbol_map
                        .free_list
                        .increment_generation();
                });
            });

            // Drop the pure functions which have been lifted. This runs once `with_heap` has
            // released the freed slots' values, which can hold their last other reference.
            self.virtual_machine
                .function_interner
                .pure_function_interner
                .retain(|_, value| crate::gc::Gc::strong_count(value) > 1);
        }
    }

    pub fn run_executable(&mut self, executable: &Executable) -> Result<Vec<SteelVal>> {
        self.virtual_machine.run_executable(executable)
    }

    /// Directly emit the expanded ast
    pub fn emit_expanded_ast(
        &mut self,
        expr: &str,
        path: Option<PathBuf>,
    ) -> Result<Vec<ExprKind>> {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .emit_expanded_ast(expr, path)
        })
    }

    fn with_sources_guard<T>(&self, func: impl FnOnce() -> T) -> T {
        let res = func();

        self.virtual_machine
            .compiler
            .write()
            .gc_sources(self.virtual_machine.function_interner.spans.values());

        res
    }

    pub fn emit_expanded_ast_without_optimizations(
        &mut self,
        expr: &str,
        path: Option<PathBuf>,
    ) -> Result<Vec<ExprKind>> {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .emit_expanded_ast_without_optimizations(expr, path)
        })
    }

    /// Emit the unexpanded AST
    pub fn emit_ast_to_string(expr: &str) -> Result<String> {
        let parsed = Self::emit_ast(expr)?;
        Ok(parsed.into_iter().map(|x| x.to_pretty(60)).join("\n\n"))
    }

    pub fn emit_ast(expr: &str) -> Result<Vec<ExprKind>> {
        let parsed: core::result::Result<Vec<ExprKind>, ParseError> =
            Parser::new(expr, SourceId::none()).collect();
        Ok(parsed?)
    }

    /// Emit the fully expanded AST as a pretty printed string
    pub fn emit_fully_expanded_ast_to_string(
        &mut self,
        expr: &str,
        path: Option<PathBuf>,
    ) -> Result<String> {
        self.with_sources_guard(|| {
            Ok(self
                .virtual_machine
                .compiler
                .write()
                .emit_expanded_ast(expr, path)?
                .into_iter()
                .map(|x| x.to_pretty(60))
                .join("\n\n"))
        })
    }

    /// Emits the fully expanded AST directly.
    pub fn emit_fully_expanded_ast(
        &mut self,
        expr: &str,
        path: Option<PathBuf>,
    ) -> Result<Vec<ExprKind>> {
        self.with_sources_guard(|| {
            self.virtual_machine
                .compiler
                .write()
                .emit_expanded_ast(expr, path)
        })
    }

    /// Registers an external value of any type as long as it implements [`FromSteelVal`](crate::rvals::FromSteelVal) and
    /// [`IntoSteelVal`](crate::rvals::IntoSteelVal). This method does the coercion to embed the type into the `Engine`'s
    /// environment with the name `name`. This function can fail only if the conversion from `T` to [`SteelVal`](crate::rvals::SteelVal) fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new();
    /// let external_value = "hello-world".to_string();
    /// vm.register_external_value("hello-world", external_value).unwrap();
    /// vm.run("hello-world").unwrap(); // Will return the string
    /// ```
    pub fn register_external_value<T: FromSteelVal + IntoSteelVal>(
        &mut self,
        name: &str,
        value: T,
    ) -> Result<&mut Self> {
        let converted = value.into_steelval()?;
        Ok(self.register_value(name, converted))
    }

    /// Registers a [`SteelVal`](crate::rvals::SteelVal) under the name `name` in the `Engine`'s internal environment.
    ///
    /// # Examples
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// use steel::rvals::SteelVal;
    ///
    /// let mut vm = Engine::new();
    /// let external_value = SteelVal::StringV("hello-world".to_string().into());
    /// vm.register_value("hello-world", external_value);
    /// vm.run("hello-world").unwrap(); // Will return the string
    /// ```
    pub fn register_value(&mut self, name: &str, value: SteelVal) -> &mut Self {
        self.register_value_inner(name, value)
    }

    pub fn update_value(&mut self, name: &str, value: SteelVal) -> Option<&mut Self> {
        let idx = self.virtual_machine.compiler.read().get_idx(name)?;

        let value = self.virtual_machine.with_heap_input(
            None,
            value,
            crate::values::closed::HeapResult::root_result,
            |_, _, value| value,
        );

        #[cfg(feature = "sync")]
        {
            self.virtual_machine
                .with_locked_env(|_, env| env.set_idx(idx, value));
        }

        #[cfg(not(feature = "sync"))]
        {
            self.virtual_machine
                .with_locked_env(|this| this.global_env.repl_set_idx(idx, value))
                .ok()?;
        }

        Some(self)
    }

    /// Registers multiple values at once
    pub fn register_values(
        &mut self,
        values: impl Iterator<Item = (String, SteelVal)>,
    ) -> &mut Self {
        for (name, value) in values {
            self.register_value(name.as_str(), value);
        }
        self
    }

    /// Registers a predicate for a given type. When embedding external values, it is convenient
    /// to be able to have a predicate to test if the given value is the specified type.
    /// In order to be registered, a type must implement [`FromSteelVal`](crate::rvals::FromSteelVal)
    /// and [`IntoSteelVal`](crate::rvals::IntoSteelVal)
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// # use steel::steel_vm::register_fn::RegisterFn;
    /// # use steel::rvals::FromSteelVal;
    /// # use steel::rvals::IntoSteelVal;
    /// # use steel::rvals::Result;
    /// # use steel::rvals::SteelVal;
    ///
    /// #[derive(Clone, Debug)]
    /// struct ExternalStruct {
    ///     value: isize,
    /// }
    ///
    /// impl ExternalStruct {
    ///     pub fn new(value: isize) -> Self {
    ///         Self {
    ///             value,
    ///         }
    ///     }
    /// }
    ///
    /// impl FromSteelVal for ExternalStruct {
    ///     fn from_steelval(val: &SteelVal) -> Result<Self> {
    ///         let value: isize = match val {
    ///             SteelVal::IntV(v) => *v,
    ///             _ => unimplemented!()
    ///         };
    ///         Ok(Self{
    ///            value,
    ///         })
    ///     }
    /// }
    ///
    /// impl IntoSteelVal for ExternalStruct {
    ///     fn into_steelval(self) -> Result<SteelVal> {
    ///         Ok(SteelVal::IntV(self.value))
    ///     }
    /// }
    ///
    /// let mut vm = Engine::new();
    ///
    /// // Register the type with the VM.
    /// vm.register_type::<ExternalStruct>("ExternalStruct?");
    ///
    /// // Register a constructor as a function with the same name as the struct.
    /// vm.register_fn("ExternalStruct", ExternalStruct::new);
    ///
    /// let _ = vm
    ///     .compile_and_run_raw_program(r#"(define new-external-struct (ExternalStruct 42))"#).unwrap(); // Returns vec![10]
    ///
    /// let extracted = vm.extract::<ExternalStruct>("new-external-struct").unwrap();
    /// assert_eq!(extracted.value, 42);
    /// ```
    pub fn register_type<T: FromSteelVal + IntoSteelVal>(
        &mut self,
        predicate_name: &'static str,
    ) -> &mut Self {
        let f = move |args: &[SteelVal]| -> Result<SteelVal> {
            if args.len() != 1 {
                stop!(ArityMismatch => format!("{} expected 1 argument, got {}", predicate_name, args.len()));
            }

            assert!(args.len() == 1);

            Ok(SteelVal::BoolV(T::from_steelval(&args[0]).is_ok()))
        };

        self.register_value(
            predicate_name,
            SteelVal::BoxedFunction(Gc::new(BoxedDynFunction::new(
                Arc::new(f),
                Some(predicate_name),
                Some(1),
            ))),
        )
    }

    /// Extracts a value with the given identifier `name` from the internal environment.
    /// If a script calculated some series of bound values, then it can be extracted this way.
    /// This will return the [`SteelVal`](crate::rvals::SteelVal), not the underlying data.
    /// To unwrap the value, use the [`extract`](crate::steel_vm::engine::Engine::extract) method and pass the type parameter.
    ///
    /// The function will return an error if the `name` is not currently bound in the `Engine`'s internal environment.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// use steel::rvals::SteelVal;
    /// let mut vm = Engine::new();
    /// vm.run("(define a 10)").unwrap();
    /// assert_eq!(vm.extract_value("a").unwrap(), SteelVal::IntV(10));
    /// ```
    pub fn extract_value(&self, name: &str) -> Result<SteelVal> {
        let idx = self.virtual_machine.compiler.read().get_idx(name).ok_or_else(throw!(
            Generic => format!("free identifier: {name} - identifier given cannot be found in the global environment")
        ))?;

        self.virtual_machine.extract_value(idx)
            .ok_or_else(throw!(
                Generic => format!("free identifier: {name} - identifier given cannot be found in the global environment")
            ))
    }

    /// Extracts a value with the given identifier `name` from the internal environment, and attempts to coerce it to the
    /// given type. This will return an error if the `name` is not currently bound in the `Engine`'s internal environment, or
    /// if the type passed in does not match the value (and thus the coercion using [`FromSteelVal`](crate::rvals::FromSteelVal) fails)
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate steel;
    /// # use steel::steel_vm::engine::Engine;
    /// let mut vm = Engine::new();
    /// vm.run("(define a 10)").unwrap();
    /// assert_eq!(vm.extract::<usize>("a").unwrap(), 10);
    /// ```
    pub fn extract<T: FromSteelVal>(&self, name: &str) -> Result<T> {
        T::from_steelval(&self.extract_value(name)?)
    }

    /// Raise the error within the stack trace
    pub fn raise_error(&self, error: SteelErr) {
        raise_error(&self.virtual_machine.compiler.read().sources, error)
    }

    /// Emit an error string reporing, the back trace.
    pub fn raise_error_to_string(&self, error: SteelErr) -> Option<String> {
        raise_error_to_string(&self.virtual_machine.compiler.read().sources, error)
    }

    pub fn add_module(&mut self, path: String) -> Result<()> {
        self.virtual_machine
            .compiler
            .write()
            .compile_module(path.into(), self.modules.clone())
    }

    pub fn modules(&self) -> MappedRwLockReadGuard<'_, crate::HashMap<PathBuf, CompiledModule>> {
        RwLockReadGuard::map(self.virtual_machine.compiler.read(), |x| x.modules())
    }

    pub fn module_metadata(&self) -> crate::HashMap<PathBuf, crate::time::SystemTime> {
        self.virtual_machine
            .compiler
            .read()
            .module_manager
            .file_metadata
            .clone()
    }

    pub fn global_exists(&self, ident: &str) -> bool {
        let spur = if let Some(spur) = InternedString::try_get(ident) {
            spur
        } else {
            return false;
        };

        self.virtual_machine
            .compiler
            .read()
            .symbol_map
            .get(&spur)
            .is_ok()
    }

    pub fn symbol_map(&self) -> MappedRwLockReadGuard<'_, SymbolMap> {
        RwLockReadGuard::map(self.virtual_machine.compiler.read(), |x| &x.symbol_map)
    }

    pub fn in_scope_macros(
        &self,
    ) -> MappedRwLockReadGuard<'_, FxHashMap<InternedString, SteelMacro>> {
        RwLockReadGuard::map(self.virtual_machine.compiler.read(), |x| &x.macro_env)
    }

    pub fn in_scope_macros_mut(
        &mut self,
    ) -> MappedRwLockWriteGuard<'_, FxHashMap<InternedString, SteelMacro>> {
        RwLockWriteGuard::map(self.virtual_machine.compiler.write(), |x| &mut x.macro_env)
    }

    // TODO: Re-implement the module path expansion
    pub fn get_module(&self, path: PathBuf) -> Result<SteelVal> {
        let module_path = path_to_module_name(path);
        self.extract_value(&module_path)
    }

    pub fn get_source_id(&self, path: &Path) -> Option<SourceId> {
        self.virtual_machine
            .compiler
            .read()
            .sources
            .get_source_id(path)
    }

    pub fn get_path_for_source_id(&self, source_id: &SourceId) -> Option<PathBuf> {
        self.virtual_machine
            .compiler
            .read()
            .sources
            .get_path(source_id)
    }

    pub fn get_source(&self, source_id: &SourceId) -> Option<Arc<Cow<'static, str>>> {
        self.virtual_machine
            .compiler
            .read()
            .sources
            .sources
            .get(*source_id)
            .cloned()
    }

    #[doc(hidden)]
    pub fn get_doc_for_identifier(&self, ident: &str) -> Option<String> {
        let value = self.extract_value(ident).ok()?;

        match self.virtual_machine.compiler.read().get_doc(value)? {
            crate::compiler::compiler::StringOrSteelString::String(s) => Some(s),
            crate::compiler::compiler::StringOrSteelString::SteelString(steel_string) => {
                Some(steel_string.as_str().to_string())
            }
        }
    }
}

// #[cfg(test)]
// mod on_progress_tests {
//     use super::*;
//     use core::cell::Cell;
//     use alloc::rc::Rc;

//     // TODO: At the moment the on progress business is turned off

//     // #[test]
//     // fn count_every_thousand() {
//     //     let mut vm = Engine::new();

//     //     let external_count = Rc::new(Cell::new(0));
//     //     let embedded_count = Rc::clone(&external_count);

//     //     vm.on_progress(move |count| {
//     //         // parameter is 'usize' - number of instructions performed up to this point
//     //         if count % 1000 == 0 {
//     //             // print out a progress log every 1000 operations
//     //             println!("Number of instructions up to this point: {}", count);
//     //             embedded_count.set(embedded_count.get() + 1);

//     //             // Returning false here would quit the evaluation of the function
//     //             return true;
//     //         }
//     //         true
//     //     });

//     //     // This should end with "Number of instructions up to this point: 4000"
//     //     vm.run(
//     //         r#"
//     //         (define (loop x)
//     //             (if (equal? x 1000)
//     //                 x
//     //                 (loop (+ x 1))))
//     //         (displayln (loop 0))
//     //     "#,
//     //     )
//     //     .unwrap();

//     //     assert_eq!(external_count.get(), 4);
//     // }
// }

fn raise_error(sources: &Sources, error: SteelErr) {
    if let Some(span) = error.span() {
        let source_id = span.source_id();

        if let Some(source_id) = source_id {
            let sources = &sources.sources;

            let file_name = sources.get_path(&source_id);

            if let Some(file_content) = sources.get(source_id) {
                // Build stack trace if we have it:
                if let Some(trace) = error.stack_trace() {
                    // TODO: Flatten recursive calls into the same stack trace
                    // and present the count
                    for dehydrated_context in trace.trace().iter().take(20) {
                        // Report a call stack with whatever we actually have,
                        if let Some(span) = dehydrated_context.span() {
                            let id = span.source_id();
                            if let Some(id) = id {
                                if let Some(source) = sources.get(id) {
                                    let trace_line_file_name = sources.get_path(&id);

                                    let resolved_file_name = trace_line_file_name
                                        .as_ref()
                                        .and_then(|x| x.to_str())
                                        .unwrap_or_default();

                                    back_trace(resolved_file_name, source, *span);
                                }
                            }
                        }
                    }
                }

                let resolved_file_name = file_name.unwrap_or_default();

                error.emit_result(resolved_file_name.to_str().unwrap(), file_content);
                return;
            }
        }
    }

    println!("Unable to locate source and span information for this error: {error}");
}

// If we are to construct an error object, emit that
pub(crate) fn raise_error_to_string(sources: &Sources, error: SteelErr) -> Option<String> {
    if let Some(span) = error.span() {
        let source_id = span.source_id();
        if let Some(source_id) = source_id {
            let sources = &sources.sources;

            let file_name = sources.get_path(&source_id);

            if let Some(file_content) = sources.get(source_id) {
                let mut back_traces = Vec::with_capacity(20);

                // Build stack trace if we have it:
                if let Some(trace) = error.stack_trace() {
                    // TODO: Flatten recursive calls into the same stack trace
                    // and present the count
                    for dehydrated_context in trace.trace().iter().take(20) {
                        // Report a call stack with whatever we actually have,
                        if let Some(span) = dehydrated_context.span() {
                            // Missing the span, its not particularly worth reporting?
                            if span.start == 0 && span.end == 0 {
                                continue;
                            }

                            let id = span.source_id();

                            if let Some(id) = id {
                                if let Some(source) = sources.get(id) {
                                    let trace_line_file_name = sources.get_path(&id);

                                    let resolved_file_name = trace_line_file_name
                                        .as_ref()
                                        .and_then(|x| x.to_str())
                                        .unwrap_or_default();

                                    let bt =
                                        back_trace_to_string(resolved_file_name, source, *span);
                                    back_traces.push(bt);
                                }
                            }
                        }
                    }
                }

                let resolved_file_name = file_name.unwrap_or_default();

                let final_error =
                    error.emit_result_to_string(resolved_file_name.to_str().unwrap(), file_content);

                back_traces.push(final_error);

                return Some(back_traces.join("\n"));
            }
        }
    }

    // println!("Unable to locate source and span information for this error: {error}");

    None
}

pub struct EngineBuilder {
    engine: Engine,
}

impl EngineBuilder {
    pub fn raw() -> Self {
        Self {
            engine: Engine::new_raw(),
        }
    }
}

#[cfg(test)]
mod engine_api_tests {
    use crate::custom_reference;

    use super::*;

    struct ReferenceStruct {
        value: usize,
    }

    impl ReferenceStruct {
        pub fn get_value(&mut self) -> usize {
            self.value
        }

        pub fn get_value_immutable(&self) -> usize {
            self.value
        }
    }

    impl CustomReference for ReferenceStruct {}
    custom_reference!(ReferenceStruct);

    #[test]
    fn test_references_in_engine() {
        let mut engine = Engine::new();
        let mut external_object = ReferenceStruct { value: 10 };

        engine.register_value("*external*", SteelVal::Void);
        engine.register_fn("external-get-value", ReferenceStruct::get_value);

        {
            let res = engine
                .run_with_reference::<ReferenceStruct, ReferenceStruct>(
                    &mut external_object,
                    "*external*",
                    "(external-get-value *external*)",
                )
                .unwrap();

            assert_eq!(res, SteelVal::IntV(10));
        }
    }

    #[test]
    fn test_references_in_engine_get_removed_after_lifetime() {
        let mut engine = Engine::new();
        let mut external_object = ReferenceStruct { value: 10 };

        engine.register_value("*external*", SteelVal::Void);
        engine.register_fn("external-get-value", ReferenceStruct::get_value);

        let res = engine
            .run_with_reference::<ReferenceStruct, ReferenceStruct>(
                &mut external_object,
                "*external*",
                "(external-get-value *external*)",
            )
            .unwrap();

        assert_eq!(res, SteelVal::IntV(10));

        // Afterwards, the value should be gone
        assert_eq!(engine.extract_value("*external*").unwrap(), SteelVal::Void);
    }

    #[test]
    fn test_immutable_references_in_engine_get_removed_after_lifetime() {
        let mut engine = Engine::new();
        let external_object = ReferenceStruct { value: 10 };

        engine.register_fn("external-get-value", ReferenceStruct::get_value);

        engine.register_fn(
            "external-get-value-imm",
            ReferenceStruct::get_value_immutable,
        );

        let res = engine
            .run_thunk_with_ro_reference::<ReferenceStruct, ReferenceStruct>(
                &external_object,
                |mut engine, value| {
                    engine.register_value("*external*", value);
                    engine
                        .compile_and_run_raw_program("(external-get-value-imm *external*)")
                        .map(|x| x.into_iter().next().unwrap())
                },
            )
            .unwrap();

        assert_eq!(res, SteelVal::IntV(10));

        // This absolutely has to fail, otherwise we're in trouble.
        assert!(engine
            .compile_and_run_raw_program("(external-get-value-imm *external*)")
            .is_err());
    }
}

#[cfg(test)]
mod engine_sandbox_tests {
    use super::*;

    #[test]
    fn sandbox() {
        let mut engine = Engine::new_sandboxed();

        assert!(engine
            .compile_and_run_raw_program(r#"(create-directory! "foo-bar")"#)
            .is_err());
    }
}

#[cfg(test)]
mod derive_macro_tests {
    use super::*;

    #[derive(steel_derive::_Steel, PartialEq, Debug)]
    #[steel(getters)]
    struct FooBar {
        baz: usize,
    }

    #[test]
    fn test_struct_registered() {
        let mut module = BuiltInModule::new("foo");
        FooBar::register_type(&mut module);
    }

    #[derive(steel_derive::_Steel, PartialEq, Debug)]
    #[steel(equality, getters, constructors)]
    enum TestEnumVariants {
        Foo,
        Bar,
        Baz(usize, usize),
        Bazinga {
            foo: usize,
            bananas: usize,
        },
        #[steel(ignore)]
        Ignored(SteelString),
    }

    fn test() {
        let mut module = BuiltInModule::new("foo");
        TestEnumVariants::register_enum_variants(&mut module);
    }

    enum Foo {
        Bananas(usize, usize, usize, usize),
        Bananas2(usize, usize, usize, usize),
    }

    #[test]
    fn test_primitives_are_registered() {
        let mut engine = Engine::new();
        let mut module = BuiltInModule::new("foo");

        TestEnumVariants::register_enum_variants(&mut module);
        engine.register_module(module);

        engine
            .run(
                r#"
(require-builtin foo)
(assert! (TestEnumVariants-Foo? (TestEnumVariants-Foo)))
(assert! (TestEnumVariants-Bar? (TestEnumVariants-Bar)))
(assert! (TestEnumVariants-Baz? (TestEnumVariants-Baz 10 20)))
(assert! (TestEnumVariants-Bazinga? (TestEnumVariants-Bazinga 100 200)))

(assert! (equal? (TestEnumVariants-Bazinga-foo (TestEnumVariants-Bazinga 100 200)) 100))
(assert! (equal? (TestEnumVariants-Bazinga-bananas (TestEnumVariants-Bazinga 100 200)) 200))
(assert! (equal? (TestEnumVariants-Baz-0 (TestEnumVariants-Baz 100 200)) 100))
(assert! (equal? (TestEnumVariants-Baz-1 (TestEnumVariants-Baz 100 200)) 200))

(assert! (not (equal? 100 (TestEnumVariants-Foo))))

            "#,
            )
            .unwrap();

        assert!(engine
            .run(r#"(TestEnumVariants-Ignored "Hello world")"#)
            .is_err())
    }
}

#[test]
fn test_steel_quote_macro() {
    use thin_vec::thin_vec;
    let foobarbaz = ExprKind::atom("foo");
    let foobarbaz_list = ExprKind::List(List::new(thin_vec![ExprKind::atom("foo")]));

    let expanded = steel_derive::internal_steel_quote! {
        (define bananas #foobarbaz)
        (define x (begin @foobarbaz_list ...))
    }
    .unwrap();

    println!("{}", expanded);
}

#[test]
fn test_raw_engine() {
    let mut engine = Engine::new_raw_no_kernel();
    engine.register_steel_module(
        "in-memory".to_owned(),
        "(provide foo) (define (foo) 10)".to_owned(),
    );

    engine.run(r#"(require "in-memory")"#).unwrap();
    let res = engine.run("(foo)").unwrap();

    assert_eq!(res[0], SteelVal::IntV(10));
}

#[test]
fn test_required_macro_expands_inside_let_body() {
    let mut engine = Engine::new();
    engine.register_steel_module(
        "twice-macro".to_owned(),
        "(provide twice) (define-syntax twice (syntax-rules () [(_ x) (* 2 x)]))".to_owned(),
    );

    engine.run(r#"(require "twice-macro")"#).unwrap();

    let res = engine
        .run(
            r#"
            (define (sum-doubled n)
              (let loop ([i 0] [acc 0])
                (if (= i n)
                    acc
                    (loop (+ i 1) (+ acc (twice i))))))
            (sum-doubled 4)
            "#,
        )
        .unwrap();
    assert_eq!(res.last().unwrap(), &SteelVal::IntV(12));

    let res = engine.run("(let ([i 3]) i (twice i))").unwrap();
    assert_eq!(res.last().unwrap(), &SteelVal::IntV(6));

    let res = engine
        .run("(let loop ([twice (lambda (x) 100)]) (twice 1))")
        .unwrap();
    assert_eq!(res.last().unwrap(), &SteelVal::IntV(100));
}

#[test]
fn test_ctx_func() {
    let mut engine = Engine::new();

    let mut module = BuiltInModule::new("test/module-ctx-func");

    module.register_fn("foo", |implicit: SteelVal| {
        println!("Called with implicit: {}", implicit);
    });

    engine.register_value("global-context", SteelVal::StringV("Hello world!".into()));

    module.supply_context_arg("global-context", "foo");

    engine.register_module(module);

    engine
        .run("(require-builtin test/module-ctx-func)")
        .unwrap();
    engine.run("(foo)").unwrap();
    engine.update_value("global-context", SteelVal::IntV(10));
    engine.run("(foo)").unwrap();
}

#[test]
fn test_ctx_func_registration() {
    let mut engine = Engine::new();

    let mut module = BuiltInModule::new("test/module-ctx-func-registration");
    engine.register_value("global-context", SteelVal::StringV("Hello world!".into()));

    module.register_fn_with_ctx("global-context", "foo", |implicit: SteelVal| {
        println!("Called with implicit: {}", implicit);
    });

    engine.register_module(module);

    engine
        .run("(require-builtin test/module-ctx-func-registration)")
        .unwrap();
    engine.run("(foo)").unwrap();
    engine.update_value("global-context", SteelVal::IntV(10));
    engine.run("(foo)").unwrap();
}

#[test]
fn test_ctx_func_registration_multiple() {
    let mut engine = Engine::new();

    let mut module = BuiltInModule::new("test/module-ctx-func-registration-multiple");
    engine.register_value("global-context", SteelVal::StringV("Hello world!".into()));

    module.register_fn_with_ctx("global-context", "foo", |implicit: SteelVal| {
        println!("Called with implicit: {}", implicit);
    });
    module.register_fn_with_ctx(
        "global-context",
        "bar",
        |implicit: SteelVal, arg: SteelVal| {
            println!("Bar Called with implicit: {}", implicit);
            println!("Bar Called with arg: {}", arg);
        },
    );

    engine.register_module(module);

    engine
        .run("(require-builtin test/module-ctx-func-registration-multiple)")
        .unwrap();
    engine.run("(bar 10)").unwrap();
    engine.update_value("global-context", SteelVal::IntV(10));
    engine.run("(bar 100)").unwrap();
}

#[cfg(test)]
mod resolver_tests {
    use super::*;

    use std::collections::HashMap;

    use crate::steel_vm::{
        builtin::BuiltInModule,
        engine::{Engine, ModuleResolver},
        register_fn::RegisterFn,
    };

    #[derive(Clone)]
    struct ModuleContainer(HashMap<String, BuiltInModule>);

    impl ModuleResolver for ModuleContainer {
        fn resolve(&self, name: &str) -> Option<BuiltInModule> {
            self.0.get(name).cloned()
        }

        fn names(&self) -> Vec<String> {
            self.0.keys().cloned().collect()
        }
    }

    impl Default for ModuleContainer {
        fn default() -> Self {
            let foo_mod = foo_module();

            Self(HashMap::from_iter([(foo_mod.name().to_string(), foo_mod)]))
        }
    }

    fn bar() -> String {
        String::from("baz")
    }

    fn foo_module() -> BuiltInModule {
        let mut module = BuiltInModule::new("foo");
        module.register_fn("bar", bar);
        module
    }

    fn engine_with_resolver(resolver: impl ModuleResolver + 'static) -> Engine {
        let mut engine = Engine::new();
        engine.register_module_resolver(resolver);
        engine
    }

    fn engine_with_modules(modules: impl Iterator<Item = BuiltInModule>) -> Engine {
        let mut engine = Engine::new();
        for module in modules {
            engine.register_module(module);
        }
        engine
    }

    #[test]
    fn with_resolver() {
        let modules = ModuleContainer::default();
        let mut engine = engine_with_resolver(modules);
        assert!(engine.run("(require-builtin foo)").is_ok());
    }

    #[test]
    fn with_modules() {
        let modules = ModuleContainer::default();
        let mut engine = engine_with_modules(modules.0.values().cloned());
        assert!(engine.run("(require-builtin foo)").is_ok());
    }

    #[test]
    fn modules_are_not_shared_between_engines() {
        let mut with_module = engine_with_modules(std::iter::once(foo_module()));
        assert!(with_module.run("(require-builtin foo)").is_ok());

        let mut without_module = Engine::new();
        let err = without_module
            .run("(require-builtin foo)")
            .expect_err("foo leaked into an engine it was never registered with");

        assert!(
            err.to_string().contains("module not found"),
            "expected foo to be unresolvable, got: {}",
            err
        );
    }

    #[test]
    fn resolvers_are_not_shared_between_engines() {
        let mut with_resolver = engine_with_resolver(ModuleContainer::default());
        assert!(with_resolver.run("(require-builtin foo)").is_ok());

        let mut without_resolver = Engine::new();
        let err = without_resolver
            .run("(require-builtin foo)")
            .expect_err("the resolver leaked into an engine it was never registered with");

        assert!(
            err.to_string().contains("module not found"),
            "expected `foo` to be unresolvable, got: {}",
            err
        );
    }
}

#[test]
fn engine_bootstrap_preserves_struct_macro() {
    for mut engine in [Engine::new(), Engine::new_sandboxed()] {
        let result = engine
            .run(
                "(struct point (x) #:mutable)
                 (define p (point 3))
                 (set-point-x! p 4)
                 (point-x p)",
            )
            .unwrap();
        assert_eq!(result.last(), Some(&SteelVal::IntV(4)));
    }
}

#[test]
fn raw_engine_native_forms_respect_lexical_shadowing() {
    let mut engine = Engine::new_raw_no_kernel();
    for name in ["struct", "define-values"] {
        for source in [
            format!("((lambda ({name}) ({name} 42)) (lambda (x) x))"),
            format!("(let (({name} (lambda (x) x))) ({name} 42))"),
            format!("((lambda ({name}) (let ((x 42)) ({name} x))) (lambda (x) x))"),
            format!("(let (({name} (lambda (x) x))) ((lambda (x) ({name} x)) 42))"),
            format!("((lambda () (define (call {name}) ({name} 42)) (call (lambda (x) x))))"),
            format!("((lambda () (define (call {name}) ((lambda (x) ({name} x)) 42)) (call (lambda (x) x))))"),
            format!("((lambda () (define (call {name}) (define (nested x) ({name} x)) (nested 42)) (call (lambda (x) x))))"),
            format!("((lambda () (define (call x) (define (nested {name}) ({name} x)) (nested (lambda (x) x))) (call 42)))"),
            format!("((lambda () (define (call . {name}) (set! {name} (lambda (x) x)) ({name} 42)) (call)))"),
            format!("((lambda () (define (call x . {name}) (set! {name} (lambda (x) x)) ({name} x)) (call 42)))"),
            format!("((lambda () (define {name} (lambda (x) x)) ({name} 42)))"),
            format!("((lambda () (define (call) ({name} 42)) (define ({name} x) x) (call)))"),
            format!("((lambda () (define call (lambda () ({name} 42))) (begin (begin (define {name} (lambda (x) x)))) (call)))"),
            format!("(let ((x 42)) (define (call) ({name} x)) (begin (define ({name} x) x)) (call))"),
            format!("(let loop ((x 42)) (define call (lambda () ({name} x))) (define {name} (lambda (x) x)) (call))"),
        ] {
            assert_eq!(
                engine
                    .run(format!(
                        "((lambda ()
                           (define result {source})
                           (struct point (value))
                           (define-values (answer) (point-value (point result)))
                           answer))"
                    ))
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_native_forms_respect_global_shadowing() {
    for name in ["struct", "define-values"] {
        for definition in [
            format!("(define ({name} x) x)"),
            format!("(define {name} (lambda (x) x))"),
            format!("(begin (begin (define ({name} x) x)))"),
        ] {
            for separate_run in [false, true] {
                let mut engine = Engine::new_raw_no_kernel();
                let call = format!("({name} 42)");
                let source = if separate_run {
                    engine.run(definition.clone()).unwrap();
                    call
                } else {
                    format!("{definition} {call}")
                };
                engine
                    .emit_expanded_ast_without_optimizations(&source, None)
                    .unwrap();
                assert_eq!(
                    engine.run(source).unwrap().last(),
                    Some(&SteelVal::IntV(42))
                );
            }
            for caller in [
                format!("(define (call) ({name} 42))"),
                format!("(define call (lambda () ({name} 42)))"),
                format!("(define (call) (let ((x 42)) ({name} x)))"),
                format!("(begin (begin (define (call) ({name} 42))))"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                let source = format!("{caller} {definition} (call)");
                engine
                    .emit_expanded_ast_without_optimizations(&source, None)
                    .unwrap();
                assert_eq!(
                    engine
                        .run(source.clone())
                        .unwrap_or_else(|error| panic!("{source}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42))
                );
            }
        }
    }
}

#[test]
fn raw_engine_native_definitions_support_forward_references() {
    for name in ["struct", "define-values"] {
        for caller in [
            format!("(define (call) ({name} 42))"),
            format!("(define-values (call) (lambda () ({name} 42)))"),
            format!("(begin (begin (struct before (x)))) (define (call) ({name} 42))"),
        ] {
            let body = format!(
                "{caller}
             (begin (begin (define-values ({name}) (lambda (x) x))))
             (call)"
            );
            for source in [
                body.clone(),
                format!("(begin {body})"),
                format!("((lambda () {body}))"),
                format!("(let () {body})"),
                format!("(let loop () {body})"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine
                    .emit_expanded_ast_without_optimizations(&source, None)
                    .unwrap_or_else(|error| panic!("{source}: {error}"));
                assert_eq!(
                    engine
                        .run(source.clone())
                        .unwrap_or_else(|error| panic!("{source}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{source}"
                );
            }
            for require in ["", "(require \"unused-module\")"] {
                let mut engine = Engine::new_raw_no_kernel();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 1)".into(),
                );
                engine.register_steel_module(
                    "native-forward-reference".into(),
                    format!("{require} (provide call) {body}"),
                );
                assert_eq!(
                    engine
                        .run("(require \"native-forward-reference\") (call)")
                        .unwrap()
                        .last(),
                    Some(&SteelVal::IntV(42))
                );
            }
        }
    }
}

#[test]
fn raw_engine_native_definitions_support_forward_references_across_expressions() {
    let declaration = "(define-syntax ignore (syntax-rules () [(ignore) 0]))";
    for name in ["struct", "define-values"] {
        for definition in [
            format!("(define-values ({name}) (lambda (x) x))"),
            format!("(define ({name} x) x)"),
        ] {
            for separator in ["((lambda () 0))", "(ignore)"] {
                // Heads expand in order, so `before` is a native struct, but bodies see every
                // definition, so `call` sees the later binding of `name`.
                let body = format!(
                    "(begin (struct before (x)))
                     (define (call) ({name} (before-x (before 42))))
                     {separator}
                     {definition}
                     (call)"
                );
                for source in [
                    body.clone(),
                    format!("(begin {body})"),
                    format!("((lambda () {body}))"),
                    format!("(let () {body})"),
                ] {
                    let mut engine = Engine::new_raw_no_kernel();
                    let source = format!("{declaration} {source}");
                    assert_eq!(
                        engine
                            .run(source.clone())
                            .unwrap_or_else(|error| panic!("{source}: {error}"))
                            .last(),
                        Some(&SteelVal::IntV(42)),
                        "{source}"
                    );
                }
                let mut engine = Engine::new_raw_no_kernel();
                let source = format!("{declaration} (provide call) {body}");
                engine.register_steel_module("native-forward-reference".into(), source.clone());
                assert_eq!(
                    engine
                        .run("(require \"native-forward-reference\") (call)")
                        .unwrap_or_else(|error| panic!("{source}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{source}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_native_definitions_predeclare_across_macro_calls() {
    let declaration = "(define-syntax ignore (syntax-rules () [(ignore) 0]))";
    for (definitions, call) in [
        ("(struct struct (x))", "(struct-x (struct 42))"),
        (
            "(struct define-values (x))",
            "(define-values-x (define-values 42))",
        ),
        // A later binding of `define-values` leaves the native form before it in place.
        (
            "(define-values (struct) (lambda (x) x)) (define (define-values . args) args)",
            "(struct 42)",
        ),
    ] {
        for (global_macro, require) in [
            (false, ""),
            (false, "(require \"unused-module\")"),
            (true, ""),
            (true, "(require \"unused-module\")"),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            let declaration = if global_macro {
                engine.run(declaration).unwrap();
                ""
            } else {
                declaration
            };
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 1)".into(),
            );
            let source = format!(
                "{require} {declaration} (provide answer)
                 (define (call) {call})
                 (ignore)
                 {definitions}
                 (define answer (call))"
            );
            engine.register_steel_module("native-predeclare".into(), source.clone());
            assert_eq!(
                engine
                    .run("(require \"native-predeclare\") answer")
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_module_local_bindings_predeclare_across_global_macro_calls() {
    for require in ["", "(require \"unused-module\")"] {
        for name in ["struct", "define-values"] {
            for definition in [
                format!("(define ({name} x) x)"),
                format!("(define-values ({name}) (lambda (x) x))"),
            ] {
                let body = format!(
                    "(begin (struct before (x)))
                     (define (nested) ({name} (before-x (before 42))))
                     (ignore)
                     {definition}
                     (nested)"
                );
                for source in [
                    format!("(define (call) {body}) (define answer (call))"),
                    format!("(define answer ((lambda () {body})))"),
                    format!("(define answer (let () {body}))"),
                    format!(
                        "(define answer
                           ((lambda ()
                              (forward (begin (ignore) (struct before (x))))
                              (define (nested) ({name} (before-x (before 42))))
                              (ignore)
                              {definition}
                              (nested))))"
                    ),
                    format!("(define answer ((lambda () (bind-name {name}) ({name} 42))))"),
                    format!("(define answer (let () (begin (bind-name {name})) ({name} 42)))"),
                ] {
                    let mut engine = Engine::new_raw_no_kernel();
                    engine
                        .run(
                            "(define-syntax ignore (syntax-rules () [(ignore) 0]))
                             (define-syntax forward (syntax-rules () [(forward expr) expr]))
                             (define-syntax bind-name
                               (syntax-rules () [(bind-name name) (define (name x) x)]))",
                        )
                        .unwrap();
                    engine.register_steel_module(
                        "unused-module".into(),
                        "(provide unused) (define unused 0)".into(),
                    );
                    engine.register_steel_module(
                        "local-predeclare".into(),
                        format!("{require} (provide answer) {source}"),
                    );
                    assert_eq!(
                        engine
                            .run("(require \"local-predeclare\") answer")
                            .unwrap_or_else(|error| panic!("{require}, {source}: {error}"))
                            .last(),
                        Some(&SteelVal::IntV(42)),
                        "{require}, {source}"
                    );
                }
            }
        }
    }
}

#[test]
fn raw_engine_native_definitions_follow_expansion_order() {
    for declaration in [
        "(struct define-values (x))",
        "(begin (begin (struct define-values (x))))",
    ] {
        let body = format!("{declaration} (define-values 42) (define-values-x (define-values 42))");
        for source in [
            body.clone(),
            format!("(begin {body})"),
            format!("((lambda () {body}))"),
            format!("(let () {body})"),
            format!("(let loop () {body})"),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .emit_expanded_ast_without_optimizations(&source, None)
                .unwrap_or_else(|error| panic!("{source}: {error}"));
            assert_eq!(
                engine
                    .run(source.clone())
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_module_native_definitions_follow_macro_expansion() {
    let declaration = "(define-syntax bind-name
                         (syntax-rules ()
                           [(bind-name name) (define (name x) x)]))";
    for (origin, name) in [
        "global",
        "global-with-import",
        "local",
        "local-with-import",
        "imported",
    ]
    .into_iter()
    .flat_map(|origin| ["struct", "define-values"].map(|name| (origin, name)))
    {
        for binding in [
            format!("(bind-name {name})"),
            format!("(begin (begin (bind-name {name})))"),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine.register_steel_module(
                "binding-macro".into(),
                format!("(provide bind-name) {declaration}"),
            );
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 1)".into(),
            );
            let prefix = match origin {
                "global" | "global-with-import" => {
                    engine.run(declaration).unwrap();
                    if origin == "global-with-import" {
                        "(require \"unused-module\")".to_owned()
                    } else {
                        String::new()
                    }
                }
                "local" => declaration.to_owned(),
                "local-with-import" => format!("(require \"unused-module\") {declaration}"),
                "imported" => "(require \"binding-macro\")".to_owned(),
                _ => unreachable!(),
            };
            engine.register_steel_module(
                "macro-binding".into(),
                format!(
                    "{prefix} (provide answer) {binding} ({name} 42)
                         (define (call) ({name} 42)) (define answer (call))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"macro-binding\") answer")
                    .unwrap_or_else(|error| panic!("{origin}, {binding}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{origin}, {binding}"
            );
        }
    }
}

#[test]
fn raw_engine_native_definitions_preserve_macro_precedence() {
    let declaration = "(define-syntax define-values
                         (syntax-rules ()
                           [(define-values (name) value) (define name 42)]))";
    let body = "(define-values (answer) 1) answer";
    for source in [
        body.to_owned(),
        format!("((lambda () {body}))"),
        format!("(let () {body})"),
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        let source = format!("{declaration} {source}");
        engine
            .emit_expanded_ast_without_optimizations(&source, None)
            .unwrap();
        assert_eq!(
            engine.run(source).unwrap().last(),
            Some(&SteelVal::IntV(42))
        );
    }
    for origin in ["global", "local", "imported"] {
        let mut engine = Engine::new_raw_no_kernel();
        let prefix = match origin {
            "global" => {
                engine.run(declaration).unwrap();
                String::new()
            }
            "local" => declaration.to_owned(),
            "imported" => {
                engine.register_steel_module(
                    "values-macro".into(),
                    format!("(provide define-values) {declaration}"),
                );
                "(require \"values-macro\")".to_owned()
            }
            _ => unreachable!(),
        };
        engine.register_steel_module(
            "macro-precedence".into(),
            format!("{prefix} (provide answer) {body}"),
        );
        assert_eq!(
            engine
                .run("(require \"macro-precedence\") answer")
                .unwrap()
                .last(),
            Some(&SteelVal::IntV(42)),
            "{origin}"
        );
    }
}

#[test]
fn raw_engine_module_native_heads_preserve_struct_macro_precedence() {
    let declaration = "(define-syntax struct
                         (syntax-rules ()
                           [(struct name) (define name 42)]))";
    for origin in [
        "global",
        "global-with-import",
        "local",
        "local-with-import",
        "imported",
    ] {
        for binding in ["(struct answer)", "(begin (begin (struct answer)))"] {
            let mut engine = Engine::new_raw_no_kernel();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 1)".into(),
            );
            // Local and imported macros must still win over a global macro with the same name.
            engine.run(declaration.replace("42", "1")).unwrap();
            let prefix = match origin {
                "global" | "global-with-import" => {
                    engine.run(declaration).unwrap();
                    if origin == "global-with-import" {
                        "(require \"unused-module\")".to_owned()
                    } else {
                        String::new()
                    }
                }
                "local" => declaration.to_owned(),
                "local-with-import" => format!("(require \"unused-module\") {declaration}"),
                "imported" => {
                    engine.register_steel_module(
                        "struct-macro".into(),
                        format!("(provide struct) {declaration}"),
                    );
                    "(require \"struct-macro\")".to_owned()
                }
                _ => unreachable!(),
            };
            engine.register_steel_module(
                "struct-precedence".into(),
                format!("{prefix} (provide answer) {binding}"),
            );
            assert_eq!(
                engine
                    .run("(require \"struct-precedence\") answer")
                    .unwrap_or_else(|error| panic!("{origin}, {binding}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{origin}, {binding}"
            );
            if origin.starts_with("global") {
                assert!(!engine.virtual_machine.compiler.read().modules()
                    [std::path::Path::new("struct-precedence")]
                .macro_map
                .contains_key(&"struct".into()));
            }
        }
    }
}

#[test]
fn raw_engine_native_forms_can_bind_their_own_names() {
    for (declaration, call) in [
        (
            "(define-values (define-values) (lambda (x) x))",
            "(define-values 42)",
        ),
        ("(struct struct (x))", "(struct-x (struct 42))"),
    ] {
        let source = format!("{declaration} {call}");
        for body in [source.clone(), format!("((lambda () {source}))")] {
            let mut engine = Engine::new_raw_no_kernel();
            assert_eq!(engine.run(body).unwrap().last(), Some(&SteelVal::IntV(42)));
        }
        let mut engine = Engine::new_raw_no_kernel();
        engine.register_steel_module(
            "native-declarations".into(),
            format!("(provide answer) {declaration} (define answer {call})"),
        );
        assert_eq!(
            engine
                .run("(require \"native-declarations\") answer")
                .unwrap()
                .last(),
            Some(&SteelVal::IntV(42))
        );
    }
}

#[test]
fn dotted_constant_survives_full_gc() {
    use crate::values::lists::Pair;

    let mut engine = Engine::new();
    let leaf = engine.run("(box 42)").unwrap().pop().unwrap();
    let value = (0..30_000).fold(leaf, |tail, _| Pair::cons(SteelVal::IntV(1), tail).into());
    let mut constants = engine.virtual_machine.compiler.read().constant_map.clone();
    let before = constants.len();
    let idx = constants.add_or_get(value);
    assert_eq!(constants.len(), before + 1);
    constants.flush();
    engine.run("(#%gc-collect) (#%gc-collect)").unwrap();
    let value = constants.get(idx);
    let mut tail = &value;
    for _ in 0..30_000 {
        let pair = tail.pair().unwrap();
        assert_eq!(pair.car_ref(), &SteelVal::IntV(1));
        tail = pair.cdr_ref();
    }
    engine.register_value("saved-leaf", tail.clone());
    assert_eq!(
        engine.run("(unbox saved-leaf)").unwrap().last(),
        Some(&SteelVal::IntV(42))
    );
}

#[test]
fn raw_engine_native_forms_respect_module_shadowing() {
    for name in ["struct", "define-values"] {
        let mut engine = Engine::new_raw_no_kernel();
        engine.register_steel_module(
            "native-shadowing".into(),
            format!("(provide call) (define (call) ({name} 42)) (begin (define ({name} x) x))"),
        );
        assert_eq!(
            engine
                .run("(require \"native-shadowing\") (call)")
                .unwrap()
                .last(),
            Some(&SteelVal::IntV(42))
        );
    }
}

#[test]
fn raw_engine_module_native_bindings_follow_deferred_global_macros() {
    for require in ["", "(require \"unused-module\")"] {
        for body in [
            "(ignore) (struct point (x)) (define answer (point-x (point 42)))",
            "(begin (ignore) (struct point (x)) (define answer (point-x (point 42))))",
            "(ignore) (define-values (x) 42) (define answer x)",
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run("(define-syntax ignore (syntax-rules () [(ignore) 0]))")
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "native-after-global".into(),
                format!(
                    "{require} (provide answer)
                 (define-syntax x (syntax-rules () [(x) 7]))
                 {body}"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"native-after-global\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {body}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{require}, {body}"
            );
        }
    }
}

#[test]
fn raw_engine_module_deferred_imported_macros_respect_value_bindings() {
    for body in [
        "(begin (ignore) (define (foo) 42) (define answer (foo)))",
        "(begin (ignore) (define (foo) 42) (ignore) (define answer (foo)))",
        "(begin (ignore) (bind-foo foo) (ignore) (define answer (foo)))",
        "(begin (ignore) (begin (define (foo) 42)) (define answer (foo)))",
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        engine
            .run(
                "(define-syntax ignore (syntax-rules () [(ignore) 0]))
                 (define-syntax bind-foo (syntax-rules () [(bind-foo name) (define (name) 42)]))",
            )
            .unwrap();
        engine.register_steel_module(
            "foo-macro".into(),
            "(provide foo) (define-syntax foo (syntax-rules () [(foo) 7]))".into(),
        );
        engine.register_steel_module(
            "deferred-value-binding".into(),
            format!("(require \"foo-macro\") (provide answer) {body}"),
        );
        assert_eq!(
            engine
                .run("(require \"deferred-value-binding\") answer")
                .unwrap_or_else(|error| panic!("{body}: {error}"))
                .last(),
            Some(&SteelVal::IntV(42)),
            "{body}"
        );
    }
}

#[test]
fn raw_engine_module_global_macros_respect_nested_template_bindings() {
    for require in ["", "(require \"unused-module\")"] {
        for name in ["struct", "define-values", "helper"] {
            for template in [
                format!("(let () (bind-name {name}) ({name} 42))"),
                format!("((lambda () (bind-name {name}) ({name} 42)))"),
                format!("(let () (begin (bind-name {name})) ({name} 42))"),
                format!("(let () (bind-name {name}) ((lambda () ({name} 42))))"),
                format!("(let () (bind-recursive {name}) ({name} #t))"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine
                    .run(format!(
                        "(define-syntax bind-name
                           (syntax-rules () [(bind-name name) (define (name x) x)]))
                         (define-syntax bind-recursive
                           (syntax-rules ()
                             [(bind-recursive name)
                              (define (name again) (if again (name #f) 42))]))
                         (define-syntax helper (syntax-rules () [(helper x) 7]))
                         (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                    ))
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "nested-template-binding".into(),
                    format!("{require} (provide answer) (define answer (make-answer))"),
                );
                assert_eq!(
                    engine
                        .run("(require \"nested-template-binding\") answer")
                        .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {template}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_respect_nested_template_parameters() {
    for require in ["", "(require \"unused-module\")"] {
        for name in ["struct", "define-values", "helper"] {
            for template in [
                format!("(bind-lambda {name} ({name} 42))"),
                format!("(bind-let {name} ({name} 42))"),
                format!("(bind-function {name} ({name} 42))"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine
                    .run(format!(
                        "(define-syntax bind-lambda
                           (syntax-rules ()
                             [(bind-lambda name body) ((lambda (name) body) (lambda (x) x))]))
                         (define-syntax bind-let
                           (syntax-rules ()
                             [(bind-let name body) (let ((name (lambda (x) x))) body)]))
                         (define-syntax bind-function
                           (syntax-rules ()
                             [(bind-function name body)
                              (let () (define (call name) body) (call (lambda (x) x)))]))
                         (define-syntax helper (syntax-rules () [(helper x) 7]))
                         (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                    ))
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "nested-template-parameter".into(),
                    format!("{require} (provide answer) (define answer (make-answer))"),
                );
                assert_eq!(
                    engine
                        .run("(require \"nested-template-parameter\") answer")
                        .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {template}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_nested_template_bindings_preserve_free_references() {
    for require in ["", "(require \"unused-module\")"] {
        for (template, expected) in [
            ("(let () (bind-name helper) (helper 42))", 42),
            ("(let () (bind-name helper) (use-helper))", 7),
            (
                "(begin (let () (bind-name helper) (helper 42)) (helper 0))",
                7,
            ),
            (
                "(begin ((lambda () (bind-name helper) (helper 42))) (helper 0))",
                7,
            ),
            ("(let () (bind-name helper) (let () (use-helper)))", 7),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(format!(
                    "(define-syntax bind-name
                       (syntax-rules () [(bind-name name) (define (name x) x)]))
                     (define-syntax helper (syntax-rules () [(helper x) 7]))
                     (define-syntax use-helper (syntax-rules () [(use-helper) (helper 0)]))
                     (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                ))
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "nested-template-free-reference".into(),
                format!(
                    "{require} (provide answer) (define (helper x) 1)
                     (define answer (make-answer))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"nested-template-free-reference\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {template}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_respect_forward_macro_definitions() {
    let declaration = "(define-syntax def (syntax-rules () [(def name) (define (name) 42)]))";
    for (require, local_declaration) in [
        ("", declaration),
        ("(require \"unused-module\")", declaration),
        ("(require \"definitions\")", ""),
    ] {
        for body in [
            "(define (call) (helper)) (def helper)",
            "(begin (define (call) (helper)) (def helper))",
            "(ignore) (define (call) (helper)) (def helper)",
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(
                    "(define-syntax helper (syntax-rules () [(helper) 7]))
                     (define-syntax ignore (syntax-rules () [(ignore) 0]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "definitions".into(),
                format!("(provide def) {declaration}"),
            );
            let source = format!("{require} {local_declaration} (provide call) {body}");
            engine.register_steel_module("forward-macro-definition".into(), source.clone());
            assert_eq!(
                engine
                    .run("(require \"forward-macro-definition\") (call)")
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_reference_scope() {
    for require in ["", "(require \"unused-module\")"] {
        for (expression, expected) in [
            ("(use-helper)", 42),
            ("(forward (use-helper))", 42),
            ("(forward-helper)", 42),
            (
                "((lambda (forward) (forward-helper)) (lambda (value) 7))",
                42,
            ),
            ("(add-helper helper)", 43),
            ("(forward helper)", 1),
            ("(use-local-helper)", 1),
            ("(bind-helper)", 7),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine.register_fn("add", |a: isize, b: isize| a + b);
            engine
                .run(
                    "(define helper 42)
                     (define-syntax use-helper (syntax-rules () [(use-helper) helper]))
                     (define-syntax forward (syntax-rules () [(forward value) value]))
                     (define-syntax forward-helper (syntax-rules () [(forward-helper) (forward helper)]))
                     (define-syntax add-helper
                       (syntax-rules () [(add-helper value) (add helper value)]))
                     (define-syntax bind-helper
                       (syntax-rules () [(bind-helper) (let ((helper 7)) helper)]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "global-macro-scope".into(),
                format!(
                    "{require} (provide answer) (define helper 1)
                     (define-syntax use-local-helper
                       (syntax-rules () [(use-local-helper) helper]))
                     (define answer {expression})"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"global-macro-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {expression}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {expression}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_imported_private_helpers() {
    for require in ["", "(require \"unused-module\")"] {
        let mut engine = Engine::new_raw_no_kernel();
        engine
            .run("(define-syntax helper (syntax-rules () [(helper) 7]))")
            .unwrap();
        engine.register_steel_module(
            "unused-module".into(),
            "(provide unused) (define unused 0)".into(),
        );
        engine.register_steel_module(
            "private-helper".into(),
            "(provide make-answer)
             (define value 42)
             (define-syntax helper (syntax-rules () [(helper) value]))
             (define-syntax make-answer (syntax-rules () [(make-answer) (helper)]))"
                .into(),
        );
        engine.register_steel_module(
            "imported-helper-scope".into(),
            format!(
                "{require} (require \"private-helper\") (provide answer)
                 (define value 1) (define answer (make-answer))"
            ),
        );
        assert_eq!(
            engine
                .run("(require \"imported-helper-scope\") answer")
                .unwrap_or_else(|error| panic!("{require}: {error}"))
                .last(),
            Some(&SteelVal::IntV(42)),
            "{require}"
        );
    }
}

#[test]
fn raw_engine_module_global_template_references_escape_module_macros() {
    for (module, expected) in [
        // An imported module's private macro must not claim a global template's reference.
        (
            "(require \"private-foo\") (provide answer) (define (second a b) b)
             (define answer (second (make-zero) (use-foo)))",
            42,
        ),
        // A global macro name passed through another macro still resolves globally.
        (
            "(provide answer) (define answer (let ((helper (lambda () 1))) (outer)))",
            42,
        ),
        (
            "(require \"unused-module\") (provide answer)
             (define answer (let ((helper (lambda () 1))) (outer)))",
            42,
        ),
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        engine
            .run(
                "(define (foo x) 42)
                 (define-syntax use-foo (syntax-rules () [(use-foo) (foo 1)]))
                 (define-syntax helper (syntax-rules () [(helper) 42]))
                 (define-syntax call-it (syntax-rules () [(call-it f) (f)]))
                 (define-syntax outer (syntax-rules () [(outer) (call-it helper)]))",
            )
            .unwrap();
        engine.register_steel_module(
            "unused-module".into(),
            "(provide unused) (define unused 0)".into(),
        );
        engine.register_steel_module(
            "private-foo".into(),
            "(provide make-zero)
             (define-syntax foo (syntax-rules () [(foo x) 7]))
             (define-syntax make-zero (syntax-rules () [(make-zero) 0]))"
                .into(),
        );
        engine.register_steel_module("template-reference-scope".into(), module.into());
        assert_eq!(
            engine
                .run("(require \"template-reference-scope\") answer")
                .unwrap_or_else(|error| panic!("{module}: {error}"))
                .last(),
            Some(&SteelVal::IntV(expected)),
            "{module}"
        );
    }
}

#[test]
fn raw_engine_module_macros_respect_optional_parameters() {
    for require in ["", "(require \"unused-module\")"] {
        for expression in [
            "((lambda ((x 42)) x))",
            "((lambda () (define (f (x 42)) x) (f)))",
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            engine
                .run("(require-builtin steel/lists as #%prim.) (require-builtin steel/meta as #%prim.)")
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "module-optional-parameters".into(),
                format!(
                    "{require} (provide answer)
                     (define-syntax x (syntax-rules () [(x) 7]))
                     (define answer {expression})"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"module-optional-parameters\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {expression}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{require}, {expression}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_native_named_runtime_functions() {
    for require in ["", "(require \"unused-module\")"] {
        for name in ["struct", "define-values"] {
            for template in [
                format!("({name} 42)"),
                format!("(begin ({name} 42))"),
                format!("((lambda () ({name} 42)))"),
                format!("(let () ({name} 42))"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine
                    .run(format!(
                        "(define ({name} value) value)
                         (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                    ))
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "native-runtime-scope".into(),
                    format!("{require} (provide answer) (define answer (make-answer))"),
                );
                assert_eq!(
                    engine
                        .run("(require \"native-runtime-scope\") answer")
                        .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {template}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_native_shaped_runtime_calls() {
    for require in ["", "(require \"unused-module\")"] {
        for (definitions, call, shadow) in [
            (
                "(define (x) 42) (define (define-values a b) a)",
                "(define-values (x) 0)",
                "(define (x) 1)",
            ),
            (
                "(define x 42) (define (fields) 0) (define (struct a b) a)",
                "(struct x (fields))",
                "(define x 1)",
            ),
        ] {
            for template in [
                call.to_owned(),
                format!("(begin {call})"),
                format!("((lambda () {call}))"),
                format!("(let () {call})"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine
                    .run(format!(
                        "{definitions}
                         (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                    ))
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "native-runtime-scope".into(),
                    format!("{require} (provide answer) {shadow} (define answer (make-answer))"),
                );
                assert_eq!(
                    engine
                        .run("(require \"native-runtime-scope\") answer")
                        .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {template}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_respect_pending_native_named_functions() {
    for require in ["", "(require \"unused-module\")"] {
        for (definitions, call) in [
            ("(define (struct value) value)", "(struct 42)"),
            ("(define (define-values value) value)", "(define-values 42)"),
            (
                "(define-values (define-values) (lambda (value) value))",
                "(define-values 42)",
            ),
            (
                "(define (x) 42) (define (define-values a b) a)",
                "(define-values (x) 0)",
            ),
            (
                "(define x 42) (define (fields) 0) (define (struct a b) a)",
                "(struct x (fields))",
            ),
        ] {
            for template in [
                call.to_owned(),
                format!("(begin {call})"),
                format!("((lambda () {call}))"),
                format!("(let () {call})"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "pending-native-scope".into(),
                    format!(
                        "{require} (provide answer)
                         (define (struct value) 1) (define (define-values value) 1)
                         (define x 1) (define (answer) (make-answer))"
                    ),
                );
                assert_eq!(
                    engine
                        .run(format!(
                            "{definitions}
                             (define-syntax make-answer
                               (syntax-rules () [(make-answer) {template}]))
                             (require \"pending-native-scope\") (answer)"
                        ))
                        .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {template}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_do_not_invent_native_bindings() {
    for require in ["", "(require \"unused-module\")"] {
        for (name, call) in [
            ("struct", "(struct marker ())"),
            ("define-values", "(define-values (marker) 0)"),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(format!(
                    "(define marker 42)
                     (define-syntax {name} (syntax-rules () [({name} a b) 0]))
                     (define-syntax make-answer
                       (syntax-rules () [(make-answer) (begin {call} marker)]))"
                ))
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "native-macro-scope".into(),
                format!(
                    "{require} (provide answer) (define marker 7) (define answer (make-answer))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"native-macro-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {name}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{require}, {name}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_template_builtin_imports() {
    for require in ["", "(require \"unused-module\")"] {
        for (template, expected) in [
            ("(let () (require-builtin steel/numbers) (+ 20 22))", 42),
            (
                "((lambda () (require-builtin steel/numbers) (+ 20 22)))",
                42,
            ),
            (
                "(let () (require-builtin steel/numbers as n:) (n:+ 20 22))",
                42,
            ),
            (
                "((lambda () (require-builtin \"steel/numbers\" as n:) (n:+ 20 22)))",
                42,
            ),
            (
                "((lambda () (define (f) (+ 20 22)) (require-builtin steel/numbers) (f)))",
                42,
            ),
            (
                "(let () (require-builtin steel/numbers) (let () (+ 20 22)))",
                42,
            ),
            (
                "(begin (let () (require-builtin steel/numbers) (+ 20 22)) (+ 20 22))",
                7,
            ),
            (
                "(begin ((lambda () (require-builtin steel/numbers) (+ 20 22))) (+ 20 22))",
                7,
            ),
            (
                "(begin (let () (require-builtin steel/numbers as n:) (n:+ 20 22)) (n:+ 20 22))",
                7,
            ),
            (
                "(let () (require-builtin steel/numbers as n:) (+ 20 22))",
                7,
            ),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            engine
                .run(format!(
                    "(define (+ a b) 7) (define (n:+ a b) 7)
                     (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                ))
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "template-builtin-scope".into(),
                format!(
                    "{require} (provide answer) (define (+ a b) 1) (define (n:+ a b) 1)
                     (define answer (make-answer))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"template-builtin-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {template}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_template_top_level_builtin_imports() {
    for require in ["", "(require \"unused-module\")"] {
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine
            .run(
                "(define (+ a b) 7)
                     (define-syntax make-answer
                       (syntax-rules ()
                         [(make-answer result)
                          (begin (require-builtin steel/numbers) (define result (+ 20 22)))]))",
            )
            .unwrap();
        engine.register_steel_module(
            "unused-module".into(),
            "(provide unused) (define unused 0)".into(),
        );
        engine.register_steel_module(
            "template-top-level-imports".into(),
            format!(
                "{require} (provide answer)
                     (define-syntax + (syntax-rules () [(+ a b) 1]))
                     (make-answer answer)"
            ),
        );
        assert_eq!(
            engine
                .run("(require \"template-top-level-imports\") answer")
                .unwrap_or_else(|error| panic!("{require}: {error}"))
                .last(),
            Some(&SteelVal::IntV(42)),
            "{require}"
        );
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_optional_parameters() {
    for require in ["", "(require \"unused-module\")"] {
        for (macro_definition, default_expression, default_expected) in [
            ("(define-syntax x (syntax-rules () [(x) 7]))", "(x)", 7),
            (
                "(define-syntax x (syntax-rules () [(x value) value]))",
                "(x 42)",
                42,
            ),
        ] {
            for expression in [
                "((lambda ((x 42)) x))",
                "((lambda ((x 7)) x) 42)",
                "((lambda (#:x (x 42)) x))",
                "((lambda (#:x (x 7)) x) #:x 42)",
                "((lambda (#:x x) x) #:x 42)",
                "((lambda ((x (answer-value))) x))",
                "((lambda (#:x (x (answer-value))) x))",
                "((lambda ((x (lambda () 42))) (x)))",
                "((lambda () (define (f (x (answer-value))) x) (f)))",
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
                engine
                    .run("(require-builtin steel/lists as #%prim.) (require-builtin steel/meta as #%prim.)")
                    .unwrap();
                engine.run(macro_definition).unwrap();
                engine
                    .run("(define-syntax answer-value (syntax-rules () [(answer-value) 42]))")
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "optional-parameters".into(),
                    format!(
                        "{require} (provide answer default-answer) (define answer {expression})
                         (define default-answer ((lambda ((x {default_expression})) x)))"
                    ),
                );
                assert_eq!(
                    engine
                        .run("(require \"optional-parameters\") answer")
                        .unwrap_or_else(|error| panic!(
                            "{require}, {macro_definition}, {expression}: {error}"
                        ))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{require}, {macro_definition}, {expression}"
                );
                assert_eq!(
                    engine.run("default-answer").unwrap().last(),
                    Some(&SteelVal::IntV(default_expected)),
                    "{require}, {macro_definition}, {default_expression}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_template_binding_scope() {
    for require in ["", "(require \"unused-module\")"] {
        for (template, expected) in [
            ("((lambda ((x 42)) x))", 42),
            ("((lambda ((x 7)) x) 42)", 42),
            ("((lambda (#:x (x 42)) x))", 42),
            ("((lambda (#:x (x 7)) x) #:x 42)", 42),
            ("((lambda (#:x x) x) #:x 42)", 42),
            ("((lambda ((x x)) x))", 7),
            ("((lambda (#:x (x x)) x))", 7),
            ("((lambda ((y x) (x 1)) y))", 7),
            ("((lambda (#:y (y x) #:x (x 1)) y))", 7),
            ("(begin ((lambda ((x 42)) x)) x)", 7),
            ("((lambda () (define (f (x 42)) x) (f)))", 42),
            ("((lambda () (define x 42) x))", 42),
            ("((lambda () (define (f) x) (define x 42) (f)))", 42),
            ("((lambda () (define (f (y x)) y) (define x 42) (f)))", 42),
            ("(begin ((lambda () (define x 42) x)) x)", 7),
            ("(let ((x 42)) x)", 42),
            ("((lambda () (struct point (x)) (point-x (point 42))))", 42),
            ("(let () (struct point (x)) (point-x (point 42)))", 42),
            (
                "((lambda () (define (f) (point-x (point 42))) (struct point (x)) (f)))",
                42,
            ),
            (
                "(begin ((lambda () (struct point (x)) (point-x (point 42)))) (point-x 0))",
                7,
            ),
            (
                "(begin (let () (struct point (x)) (point-x (point 42))) (point-x 0))",
                7,
            ),
            ("((lambda (x (y x)) y) 42)", 42),
            ("((lambda (x #:y (y x)) y) 42)", 42),
            ("(let ((x x)) x)", 7),
            ("(begin (let ((x 42)) x) x)", 7),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            engine
                .run("(require-builtin steel/lists as #%prim.) (require-builtin steel/meta as #%prim.)")
                .unwrap();
            engine
                .run(format!(
                    "(define x 7) (define (point-x value) 7)
                     (define-syntax make-answer (syntax-rules () [(make-answer) {template}]))"
                ))
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "template-binding-scope".into(),
                format!(
                    "{require} (provide answer) (define x 1) (define (point-x value) 1)
                     (define answer (make-answer))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"template-binding-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {template}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {template}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_match_literals_against_module_bindings() {
    for require in ["", "(require \"unused-module\")"] {
        for binding in [
            "(define tag 0)",
            "(require \"tags\")",
            "(struct tag ())",
            "(define-values (tag) 0)",
        ] {
            for body in [
                format!("{binding} (define answer (classify tag))"),
                format!("(define (call) (classify tag)) {binding} (define answer (call))"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine
                    .run(
                        "(define-syntax classify
                           (syntax-rules (tag) [(classify tag) 1] [(classify other) 2]))",
                    )
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module("tags".into(), "(provide tag) (define tag 0)".into());
                engine.register_steel_module(
                    "literal-module-bindings".into(),
                    format!("{require} (provide answer) {body}"),
                );
                assert_eq!(
                    engine
                        .run("(require \"literal-module-bindings\") answer")
                        .unwrap_or_else(|error| panic!("{require}, {body}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(2)),
                    "{require}, {body}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_literal_reference_scope() {
    for require in ["", "(require \"unused-module\")"] {
        for (expression, expected) in [
            ("(outer)", 1),
            ("(outer-via-forward)", 1),
            ("(forward tag)", 2),
            ("(let ((tag 0)) (outer))", 1),
            ("(let ((tag 0)) (forward tag))", 2),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(
                    "(define-syntax classify
                       (syntax-rules (tag) [(classify tag) 1] [(classify other) 2]))
                     (define-syntax outer (syntax-rules () [(outer) (classify tag)]))
                     (define-syntax forward
                       (syntax-rules () [(forward value) (classify value)]))
                     (define-syntax outer-via-forward
                       (syntax-rules () [(outer-via-forward) (forward tag)]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "literal-reference-scope".into(),
                format!("{require} (provide answer) (define tag 0) (define answer {expression})"),
            );
            assert_eq!(
                engine
                    .run("(require \"literal-reference-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {expression}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {expression}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_lexical_reference_scope() {
    for require in ["", "(require \"unused-module\")"] {
        for (expression, expected) in [
            ("(let ((helper 1)) (use-helper))", 42),
            ("((lambda (helper) (use-helper)) 1)", 42),
            ("(let ((helper 1)) (forward (use-helper)))", 42),
            ("(let ((helper 1)) (forward helper))", 1),
            ("(let ((helper 1)) (bind-helper))", 7),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(
                    "(define helper 42)
                     (define-syntax use-helper (syntax-rules () [(use-helper) helper]))
                     (define-syntax forward (syntax-rules () [(forward value) value]))
                     (define-syntax bind-helper
                       (syntax-rules () [(bind-helper) (let ((helper 7)) helper)]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "lexical-reference-scope".into(),
                format!("{require} (provide answer) (define answer {expression})"),
            );
            assert_eq!(
                engine
                    .run("(require \"lexical-reference-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {expression}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {expression}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_respect_builtin_imports() {
    for require in ["", "(require \"unused-module\")"] {
        for (body, expected) in [
            ("(require-builtin steel/numbers) (define answer (+ 20 22))", 42),
            ("(begin (require-builtin steel/numbers) (define answer (+ 20 22)))", 42),
            ("(define answer (let () (require-builtin steel/numbers) (+ 20 22)))", 42),
            ("(define answer ((lambda () (require-builtin steel/numbers) (+ 20 22))))", 42),
            ("(require-builtin \"steel/numbers\") (define answer (+ 20 22))", 42),
            ("(define answer ((lambda () (require-builtin steel/numbers as n:) (n:+ 20 22))))", 42),
            ("(define answer (let () (require-builtin \"steel/numbers\" as n:) (n:+ 20 22)))", 42),
            ("(let () (require-builtin steel/numbers) (+ 20 22)) (define answer (+ 20 22))", 7),
            ("(define answer (begin ((lambda () (require-builtin steel/numbers) (+ 20 22))) (+ 20 22)))", 7),
            ("(define answer (begin (let () (require-builtin steel/numbers) (+ 20 22)) (+ 20 22)))", 7),
            ("(require-builtin steel/numbers as n:) (define answer (+ 20 22))", 7),
            ("(define answer ((lambda () (import-numbers) (+ 20 22))))", 42),
            ("(begin (require-builtin steel/numbers) (define answer (global-add)))", 7),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            engine
                .run(
                    "(define-syntax + (syntax-rules () [(+ a b) 7]))
                     (define-syntax n:+ (syntax-rules () [(n:+ a b) 7]))
                     (define-syntax global-add (syntax-rules () [(global-add) (+ 20 22)]))
                     (define-syntax import-numbers
                       (syntax-rules () [(import-numbers) (require-builtin steel/numbers)]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "builtin-import-scope".into(),
                format!("{require} (provide answer) {body}"),
            );
            assert_eq!(
                engine
                    .run("(require \"builtin-import-scope\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {body}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(expected)),
                "{require}, {body}"
            );
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_binding_errors() {
    use crate::rerrs::ErrorKind::{ArityMismatch, BadSyntax};

    for require in ["", "(require \"unused-module\")"] {
        for (expression, kind, message) in [
            (
                "(lambda ((x 1 2)) x)",
                BadSyntax,
                "malformed default argument",
            ),
            (
                "(lambda (#:x (x)) x)",
                BadSyntax,
                "Missing default argument for keyword",
            ),
            (
                "(lambda (#:x) 42)",
                BadSyntax,
                "keyword arg missing variable name",
            ),
            (
                "(lambda ((x 1) y) x)",
                BadSyntax,
                "positional arg without default",
            ),
            (
                "(require-builtin)",
                ArityMismatch,
                "require-builtin malformed",
            ),
            (
                "(require-builtin 42)",
                ArityMismatch,
                "require-builtin malformed",
            ),
            (
                "(require-builtin steel/numbers as)",
                ArityMismatch,
                "require-builtin malformed",
            ),
            (
                "(require-builtin steel/numbers as \"n:\")",
                ArityMismatch,
                "require-builtin malformed",
            ),
            (
                "(require-builtin missing-module)",
                BadSyntax,
                "require-builtin: module not found: missing-module",
            ),
            (
                "(require-builtin \"missing-module\" as n:)",
                BadSyntax,
                "require-builtin: module not found: missing-module",
            ),
        ] {
            for body in [expression, "(invalid-binding)"] {
                let mut engine = Engine::new_raw_no_kernel();
                crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
                engine
                    .run(format!(
                        "(define-syntax x (syntax-rules () [(x) 7]))
                     (define-syntax invalid-binding
                       (syntax-rules () [(invalid-binding) {expression}]))"
                    ))
                    .unwrap();
                engine.register_steel_module(
                    "unused-module".into(),
                    "(provide unused) (define unused 0)".into(),
                );
                engine.register_steel_module(
                    "binding-errors".into(),
                    format!("{require} (provide answer) (define answer {body})"),
                );
                let error = engine.run("(require \"binding-errors\")").unwrap_err();
                assert_eq!(
                    error.kind(),
                    kind,
                    "{require}, {expression}, {body}: {error}"
                );
                assert!(
                    error.to_string().contains(message),
                    "{require}, {expression}, {body}: {error}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_global_macros_preserve_native_bindings() {
    for require in ["", "(require \"unused-module\")"] {
        for body in [
            "(struct point (x)) (point-x (point 42))",
            "(define-values (x) 42) x",
            "(define-values (x) (answer-value)) x",
            "(let () (struct point (x)) (point-x (point 42)))",
            "(let () (define-values (x) 42) x)",
            "(begin (struct point (x)) (point-x (point 42)))",
            "(begin (define-values (x) 42) x)",
            "(define-values (x) (lambda () 42)) (x)",
            "(let ((struct (lambda (value) value))) (struct (answer-value)))",
            "(let ((define-values (lambda (value) value))) (define-values (answer-value)))",
            "(make-point point x) (point-x (point 42))",
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(
                    "(define-syntax x (syntax-rules () [(x) 7]))
                     (define-syntax answer-value (syntax-rules () [(answer-value) 42]))
                     (define-syntax make-point
                       (syntax-rules () [(make-point name field) (struct name (field))]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            engine.register_steel_module(
                "global-macro-bindings".into(),
                format!("{require} (provide answer) (define (f) {body}) (define answer (f))"),
            );
            assert_eq!(
                engine
                    .run("(require \"global-macro-bindings\") answer")
                    .unwrap_or_else(|error| panic!("{require}, {body}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{require}, {body}"
            );
        }
    }
}

#[test]
fn raw_engine_module_native_forms_preserve_value_precedence_over_global_macros() {
    for name in ["struct", "define-values"] {
        for definition in [
            format!("(define ({name} x) x)"),
            "(require \"native-functions\")".to_owned(),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run(format!(
                    "(define-syntax {name} (syntax-rules () [({name} x) 1]))"
                ))
                .unwrap();
            engine.register_steel_module(
                "native-functions".into(),
                format!("(provide {name}) (define ({name} x) x)"),
            );
            engine.register_steel_module(
                "native-shadowing".into(),
                format!(
                    "{definition} (provide answer) ({name} 42)
                         (define (call) ({name} 42)) (define answer (call))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"native-shadowing\") answer")
                    .unwrap_or_else(|error| panic!("{name}, {definition}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{name}, {definition}"
            );
        }
    }
}

#[test]
fn raw_engine_module_runtime_define_values_does_not_bind_call_arguments() {
    for definition in [
        "(define (define-values a b) b)",
        "(begin (begin (define (define-values a b) b)))",
        "(require \"runtime-values\")",
        "(require (only-in \"runtime-values\" (define-values define-values)))",
        "(require (only-in \"runtime-values\" (runtime-values define-values)))",
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        engine.run("(define (global-fn) 1)").unwrap();
        engine.register_steel_module(
            "runtime-values".into(),
            "(provide define-values runtime-values)
             (define (define-values a b) b) (define (runtime-values a b) b)"
                .into(),
        );
        engine.register_steel_module(
            "runtime-call".into(),
            format!(
                "{definition} (provide answer)
                 (define-values (global-fn) 42)
                 (define answer (define-values (global-fn) 42))"
            ),
        );
        assert_eq!(
            engine
                .run("(require \"runtime-call\") answer")
                .unwrap_or_else(|error| panic!("{definition}: {error}"))
                .last(),
            Some(&SteelVal::IntV(42)),
            "{definition}"
        );
        assert_eq!(engine.run("(global-fn)").unwrap(), [SteelVal::IntV(1)]);
    }
}

#[test]
fn raw_engine_module_native_forms_respect_runtime_imports() {
    for (name, prefix, suffix) in [
        ("struct", "st", "ruct"),
        ("define-values", "define-", "values"),
    ] {
        for (exported, require) in [
            (name, "\"native-functions\"".to_owned()),
            (name, format!("(only-in \"native-functions\" {name})")),
            (
                "identity",
                format!("(only-in \"native-functions\" (identity {name}))"),
            ),
            (suffix, format!("(prefix-in {prefix} \"native-functions\")")),
            (
                "identity",
                format!("(prefix-in {prefix} (only-in \"native-functions\" (identity {suffix})))"),
            ),
        ] {
            // Contract exports use this spec after their contract macro has expanded.
            for provide in [
                exported.to_owned(),
                format!("(%require-ident-spec {exported} {exported})"),
            ] {
                let mut engine = Engine::new_raw_no_kernel();
                engine.register_steel_module(
                    "native-functions".into(),
                    format!(
                        "(provide {provide} unused) (define ({exported} x) x) (define unused 0)"
                    ),
                );
                engine.register_steel_module(
                    "native-imports".into(),
                    format!(
                        "(require {require}) (provide answer) ({name} 42)
                             (define (call) ({name} 42)) (define answer (call))"
                    ),
                );
                assert_eq!(
                    engine
                        .run("(require \"native-imports\") answer")
                        .unwrap_or_else(|error| panic!("{provide}, {require}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(42)),
                    "{provide}, {require}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_native_forms_ignore_unbound_import_names() {
    for require in [
        "(only-in \"native-functions\" unused)",
        "(only-in \"native-functions\" (struct make-struct) (define-values make-values))",
        "(prefix-in imported: \"native-functions\")",
        "(only-in \"native-macro\" (struct bind-answer))",
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        engine.register_steel_module(
            "native-functions".into(),
            "(provide struct define-values unused)
             (define (struct x) x) (define (define-values x) x) (define unused 0)"
                .into(),
        );
        engine.register_steel_module(
            "native-macro".into(),
            "(provide struct)
             (define-syntax struct (syntax-rules () [(struct name) (define name 1)]))"
                .into(),
        );
        engine.register_steel_module(
            "native-imports".into(),
            format!(
                "(require {require}) (provide answer)
                     (struct point (x)) (define-values (answer) (point-x (point 42)))"
            ),
        );
        assert_eq!(
            engine
                .run("(require \"native-imports\") answer")
                .unwrap_or_else(|error| panic!("{require}: {error}"))
                .last(),
            Some(&SteelVal::IntV(42)),
            "{require}"
        );
    }
}

#[test]
fn kernel_engine_module_macros_do_not_leak_from_main() {
    let definition = "(define-syntax foo (syntax-rules () [(foo) 99]))";
    for (setup, main) in [
        ("", "(require \"foo-macro\")"),
        ("(require \"foo-macro\")", ""),
        ("", definition),
        (definition, ""),
    ] {
        for expanded_ast in [false, true] {
            let mut engine = Engine::new();
            engine.run("(define (foo) 5)").unwrap();
            engine.register_steel_module("foo-macro".into(), format!("(provide foo) {definition}"));
            engine.register_steel_module(
                "runtime-reference".into(),
                "(provide g) (define (g) (foo))".into(),
            );
            engine.run(setup).unwrap();
            let source = format!("{main} (require \"runtime-reference\") (g) (foo)");
            if expanded_ast {
                let ast = engine
                    .emit_expanded_ast_without_optimizations(&source, None)
                    .unwrap();
                assert!(
                    ast.iter().any(|expr| expr.to_string().contains("(foo)")),
                    "{setup}, {source}: {ast:?}"
                );
                assert_eq!(ast.last().unwrap().to_string(), "99", "{setup}, {source}");
            } else {
                let values = engine.run(source.clone()).unwrap();
                assert_eq!(
                    &values[values.len() - 2..],
                    &[SteelVal::IntV(5), SteelVal::IntV(99)],
                    "{setup}, {source}"
                );
            }
        }
    }
}

#[test]
fn kernel_engine_module_prelude_macros_survive_main_shadowing() {
    for shadow in [
        "",
        "(define-syntax when (syntax-rules () [(when test body) 99]))",
    ] {
        // Kernel transformers can leave prelude syntax for the late module passes.
        for body in ["(when #t 5)", "(module-prelude)"] {
            for expanded_ast in [false, true] {
                let mut engine = Engine::new();
                engine.register_steel_module(
                    "uses-prelude".into(),
                    format!("(provide g) (define (g) {body})"),
                );
                let source = format!(
                    "{shadow}
                     (defmacro (module-prelude stx) '(when #t 5))
                     (require \"uses-prelude\") (g) (when #t 5)"
                );
                if expanded_ast {
                    let ast = engine
                        .emit_expanded_ast_without_optimizations(&source, None)
                        .unwrap();
                    let expanded = ast
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("\n");
                    assert!(!expanded.contains("(when "), "{source}: {expanded}");
                    assert!(
                        !expanded.contains("(module-prelude)"),
                        "{source}: {expanded}"
                    );
                    assert!(expanded.contains("(if "), "{source}: {expanded}");
                    if !shadow.is_empty() {
                        assert_eq!(ast.last().unwrap().to_string(), "99", "{source}");
                    }
                } else {
                    let values = engine.run(source.clone()).unwrap();
                    let main_value = if shadow.is_empty() { 5 } else { 99 };
                    assert_eq!(
                        &values[values.len() - 2..],
                        &[SteelVal::IntV(5), SteelVal::IntV(main_value)],
                        "{source}"
                    );
                }
            }
        }
    }
}

#[test]
fn raw_engine_lifted_private_macros_do_not_leak_into_unrelated_modules() {
    for (setup, main) in [
        ("", "(require \"pb\") (answer)"),
        ("", "(require \"pa\") (require \"pb\") (answer)"),
        ("(require \"pa\")", "(require \"pb\") (answer)"),
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        engine.register_steel_module(
            "pa".into(),
            "(define-syntax helper (syntax-rules () [(helper) 7]))".into(),
        );
        engine.register_steel_module(
            "pb".into(),
            "(provide answer)
             (define-syntax use-helper (syntax-rules () [(use-helper) (helper)]))
             (define (answer) (define (helper) 42) (use-helper))"
                .into(),
        );
        if !setup.is_empty() {
            engine.run(setup).unwrap();
        }
        let error = engine.run(main).expect_err(main);
        assert_eq!(
            error.kind(),
            crate::rerrs::ErrorKind::FreeIdentifier,
            "{setup}, {main}: {error}"
        );
    }
}

#[test]
fn raw_engine_lifted_module_macros_do_not_claim_global_template_references() {
    for (setup, main, expected) in [
        (
            "(require \"lifted\")
             (define (foo x) 42)
             (define-syntax use-foo (syntax-rules () [(use-foo) (foo 1)]))",
            "(require \"global-reference\") (answer)",
            42,
        ),
        (
            "",
            "(require \"lifted\")
             (define (foo x) 42)
             (define-syntax use-foo (syntax-rules () [(use-foo) (foo 1)]))
             (require \"global-reference\")
             (answer)",
            42,
        ),
        // A lifted macro's own template still reaches its module's private macros.
        (
            "(require \"lifted\") (define-syntax use-foo (syntax-rules () [(use-foo) (use-it)]))",
            "(require \"global-reference\") (answer)",
            7,
        ),
    ] {
        let mut engine = Engine::new_raw_no_kernel();
        engine.register_steel_module(
            "lifted".into(),
            "(provide use-it)
             (define-syntax foo (syntax-rules () [(foo x) 7]))
             (define-syntax use-it (syntax-rules () [(use-it) (foo 0)]))"
                .into(),
        );
        engine.register_steel_module(
            "global-reference".into(),
            "(provide answer) (define (answer) (use-foo))".into(),
        );
        if !setup.is_empty() {
            engine.run(setup).unwrap();
        }
        assert_eq!(
            engine
                .run(main)
                .unwrap_or_else(|error| panic!("{main}: {error}"))
                .last(),
            Some(&SteelVal::IntV(expected)),
            "{main}"
        );
    }
}

#[test]
fn raw_engine_module_top_level_definitions_shadow_module_macros() {
    let declaration = "(define-syntax foo (syntax-rules () [(foo) (undefined-function)]))";
    for (require, local_declaration) in [("", declaration), ("(require \"foo-macro\")", "")] {
        for prefix in ["", "(ignore)"] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run("(define-syntax ignore (syntax-rules () [(ignore) 0]))")
                .unwrap();
            engine
                .register_steel_module("foo-macro".into(), format!("(provide foo) {declaration}"));
            let source = format!(
                "{require} (provide answer) {local_declaration} {prefix}
                 (define answer 0) (define (foo) (set! answer 42)) (foo)"
            );
            engine.register_steel_module("top-level-shadow".into(), source.clone());
            assert_eq!(
                engine
                    .run("(require \"top-level-shadow\") answer")
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_module_deferred_begin_definitions_shadow_macros() {
    let declaration = "(define-syntax foo (syntax-rules () [(foo) (undefined-function)]))";
    for (require, local_declaration) in [("", declaration), ("(require \"foo-macro\")", "")] {
        for prefix in ["", "(ignore)"] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run("(define-syntax ignore (syntax-rules () [(ignore) 0]))")
                .unwrap();
            engine
                .register_steel_module("foo-macro".into(), format!("(provide foo) {declaration}"));
            let source = format!(
                "{require} (provide answer) {local_declaration} (define answer 0) {prefix}
                 (begin (define (foo) (set! answer 42)) (foo))"
            );
            engine.register_steel_module("begin-shadow".into(), source.clone());
            assert_eq!(
                engine
                    .run("(require \"begin-shadow\") answer")
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_module_deferred_private_macros_stay_in_their_expansion() {
    for definition in [
        "(define-syntax foo (syntax-rules () [(foo x) 42]))",
        "(define (foo x) 42)",
    ] {
        for prefix in ["", "(ignore)"] {
            let mut engine = Engine::new_raw_no_kernel();
            engine
                .run("(define-syntax ignore (syntax-rules () [(ignore) 0]))")
                .unwrap();
            engine.register_steel_module(
                "private-foo".into(),
                "(provide use-it)
                 (define-syntax foo (syntax-rules () [(foo x) 7]))
                 (define-syntax use-it (syntax-rules () [(use-it) (foo 0)]))"
                    .into(),
            );
            let source = format!(
                "(require \"private-foo\") (provide answer) {definition} {prefix}
                 (begin (use-it) (define answer (foo 1)))"
            );
            engine.register_steel_module("private-scope".into(), source.clone());
            assert_eq!(
                engine
                    .run("(require \"private-scope\") answer")
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }
    }
}

#[test]
fn raw_engine_module_native_forms_ignore_runtime_bindings() {
    for name in ["struct", "define-values"] {
        for body in [
            "(struct point (x)) (define answer (point-x (point 42)))",
            "(define-values (answer) 42)",
            "(define (f) (struct point (x)) (point-x (point 42))) (define answer (f))",
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            engine.run(format!("(define ({name} a b) 0)")).unwrap();
            engine
                .register_steel_module("runtime-shadow".into(), format!("(provide answer) {body}"));
            assert_eq!(
                engine
                    .run("(require \"runtime-shadow\") answer")
                    .unwrap_or_else(|error| panic!("{name}, {body}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{name}, {body}"
            );
        }
    }
}

#[test]
fn bodies_see_later_definitions_after_top_level_passes() {
    for kernel in [false, true] {
        for require in [None, Some(""), Some("(require \"unused-module\")")] {
            for (body, expected) in [
                ("(define (g) (define (f) (helper)) (define (helper) 42) (f)) (define answer (g))", 42),
                ("(define answer ((lambda () (define (f) (helper)) (define (helper) 42) (f))))", 42),
                ("(define answer (let () (define (f) (helper)) (begin (define (helper) 42)) (f)))", 42),
                ("(define answer ((lambda () (define (g) (define (helper) 42) (helper)) (define (sibling) (helper)) (g) (sibling))))", 7),
                ("(define answer ((lambda () (define (g) (define (helper) 42) (helper)) (g) (helper))))", 7),
            ] {
                let mut engine = if kernel {
                    Engine::new()
                } else {
                    Engine::new_raw_no_kernel()
                };
                let macro_definition = "(define-syntax helper (syntax-rules () [(helper) 7]))";
                let source = if let Some(require) = require {
                    // Kernel-backed modules resolve this as a runtime global, not main's macro.
                    if kernel {
                        engine.run("(define (helper) 7)").unwrap();
                    }
                    engine.run(macro_definition).unwrap();
                    engine.register_steel_module(
                        "unused-module".into(),
                        "(provide unused) (define unused 0)".into(),
                    );
                    engine.register_steel_module(
                        "later-definitions".into(),
                        format!("{require} (provide answer) {body}"),
                    );
                    "(require \"later-definitions\") answer".to_string()
                } else {
                    format!("{macro_definition} {body} answer")
                };
                assert_eq!(
                    engine
                        .run(source)
                        .unwrap_or_else(|error| panic!("kernel={kernel}, {require:?}, {body}: {error}"))
                        .last(),
                    Some(&SteelVal::IntV(expected)),
                    "kernel={kernel}, {require:?}, {body}"
                );
                assert_eq!(
                    engine.run("(helper)").unwrap().last(),
                    Some(&SteelVal::IntV(7)),
                    "kernel={kernel}, {require:?}, {body}"
                );
            }
        }
    }
}

#[test]
fn raw_engine_module_bodies_see_later_builtin_imports() {
    for require in ["", "(require \"unused-module\")"] {
        for body in [
            "(define (f) (define (g) (+ 20 22)) (require-builtin steel/numbers) (g))
             (define answer (f))",
            "(make-answer answer)",
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            engine
                .run(
                    "(define-syntax + (syntax-rules () [(+ a b) 7]))
                     (define-syntax make-answer
                       (syntax-rules ()
                         [(make-answer result)
                          (define result
                            ((lambda ()
                               (define (g) (+ 20 22))
                               (require-builtin steel/numbers)
                               (g))))]))",
                )
                .unwrap();
            engine.register_steel_module(
                "unused-module".into(),
                "(provide unused) (define unused 0)".into(),
            );
            let source = format!("{require} (provide answer) {body}");
            engine.register_steel_module("later-builtin-imports".into(), source.clone());
            assert_eq!(
                engine
                    .run("(require \"later-builtin-imports\") answer")
                    .unwrap_or_else(|error| panic!("{source}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{source}"
            );
        }

        // A module's top level cannot reference a builtin before importing it, but the import
        // still shadows the global macro rather than letting it capture the call.
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine
            .run("(define-syntax + (syntax-rules () [(+ a b) 7]))")
            .unwrap();
        engine.register_steel_module(
            "unused-module".into(),
            "(provide unused) (define unused 0)".into(),
        );
        engine.register_steel_module(
            "top-level-builtin-import".into(),
            format!(
                "{require} (provide answer)
                 (define (f) (+ 20 22)) (require-builtin steel/numbers) (define answer (f))"
            ),
        );
        let error = engine
            .run("(require \"top-level-builtin-import\") answer")
            .unwrap_err();
        assert_eq!(
            error.kind(),
            crate::rerrs::ErrorKind::FreeIdentifier,
            "{require}: {error}"
        );
    }
}

#[test]
fn raw_engine_rejects_improper_definitions() {
    let mut engine = Engine::new_raw_no_kernel();
    for source in ["(define x . 1)", "(define (f x) . x)"] {
        assert!(engine.run(source).is_err(), "{source}");
    }
}

#[test]
fn raw_engine_immutable_structs() {
    let mut engine = Engine::new_raw_no_kernel();
    engine
        .run("(struct point (x y)) (struct other (x y)) (define p (point 3 4))")
        .unwrap();
    assert_eq!(engine.run("(point-x p)").unwrap()[0], SteelVal::IntV(3));
    assert_eq!(engine.run("(point? p)").unwrap()[0], SteelVal::BoolV(true));
    assert_eq!(engine.run("(other? p)").unwrap()[0], SteelVal::BoolV(false));
    assert!(engine.run("(other-x p)").is_err());
    assert!(engine.run("(point 1)").is_err());
    assert!(engine.run("(struct mutable (x) #:mutable)").is_err());
    assert!(engine.run("(struct duplicate (x x))").is_err());
    assert!(engine.run("(struct invalid (1))").is_err());
    assert!(engine.run("make-struct-type").is_err());
    engine.register_steel_module(
        "shapes".into(),
        "(provide box box? box-value) (struct box (value))".into(),
    );
    engine.run("(require \"shapes\")").unwrap();
    assert_eq!(
        engine.run("(box-value (box 9))").unwrap()[0],
        SteelVal::IntV(9)
    );
    assert_eq!(engine.run("((lambda (#%immutable-struct-type #%immutable-struct-binding) (struct local (field)) (local-field (local 11))) #f #f)").unwrap()[0], SteelVal::IntV(11));
    engine.run("(define (make-local value #%immutable-struct-type #%immutable-struct-binding) (struct local (field)) (local-field (local value)))").unwrap();
    assert_eq!(
        engine.run("(make-local 12 #f #f)").unwrap()[0],
        SteelVal::IntV(12)
    );
}

#[test]
fn raw_engine_immutable_struct_functions_round_trip() {
    let mut engine = Engine::new_raw_no_kernel();
    crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
    engine
        .run(
            "(require-builtin steel/meta)
             (require-builtin steel/lists)
             (define (round-trip function)
               (deserialize-value (bytes->serialized (serialized->bytes (serialize-value function)))))",
        )
        .unwrap();
    assert_eq!(
        engine
            .run(
                "((lambda ()
                    (struct serialized-point (x y))
                    (define restored-point (round-trip serialized-point))
                    (define restored-point? (round-trip serialized-point?))
                    (define restored-x (round-trip serialized-point-x))
                    (define restored-y (round-trip serialized-point-y))
                    (define p (restored-point 3 4))
                    (list (restored-point? p)
                          (restored-point? #f)
                          (serialized-point-x p)
                          (restored-x (serialized-point 5 6))
                          (restored-y p))))",
            )
            .unwrap(),
        [SteelVal::ListV(
            vec![
                SteelVal::BoolV(true),
                SteelVal::BoolV(false),
                SteelVal::IntV(3),
                SteelVal::IntV(5),
                SteelVal::IntV(4),
            ]
            .into()
        )]
    );
}

#[test]
fn raw_engine_definition_helpers_round_trip_in_closures() {
    let mut engine = Engine::new_raw_no_kernel();
    crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
    engine
        .run(
            "(require-builtin steel/meta)
             (define (round-trip function)
               (deserialize-value (bytes->serialized (serialized->bytes (serialize-value function)))))",
        )
        .unwrap();
    for body in [
        "(struct point (x)) (point-x (point 42))",
        "(define-values (x y) '(1 42)) y",
    ] {
        engine.run(format!("(define (f) {body})")).unwrap();
        assert_eq!(
            engine.run("((round-trip f))").unwrap(),
            [SteelVal::IntV(42)]
        );
    }
}

#[test]
fn symbol_identity_is_independent_of_allocation() {
    let mut engine = Engine::new_raw_no_kernel();
    crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
    engine
        .run("(require-builtin steel/equality) (require-builtin steel/lists)")
        .unwrap();
    assert_eq!(
        engine.run("(eq? 'a (car '(a)))").unwrap()[0],
        SteelVal::BoolV(true)
    );
    assert_eq!(
        engine.run("(eq? 'a (car '(b)))").unwrap()[0],
        SteelVal::BoolV(false)
    );
    assert_eq!(
        engine.run("(eq? 'a (car '(a . b)))").unwrap()[0],
        SteelVal::BoolV(true)
    );
    assert_eq!(
        engine.run("(eq? 'b (cdr '(a . b)))").unwrap()[0],
        SteelVal::BoolV(true)
    );
    assert_eq!(
        engine.run("(eq? 'a (car (car '((a . 1)))))").unwrap()[0],
        SteelVal::BoolV(true)
    );
}

#[test]
fn engine_define_values_preserves_module_exports() {
    let mut engine = Engine::new();
    engine
        .run(
            "(define-syntax define-values
           (syntax-rules ()
             [(define-values (a b) expression)
              (begin (define temporary expression)
                     (define a (car temporary)) (define b (car (cdr temporary))))]))",
        )
        .unwrap();
    engine.register_steel_module(
        "values-module".into(),
        "(provide a b) (define-values (a b) '(3 4))".into(),
    );
    engine.run("(require \"values-module\")").unwrap();
    assert_eq!(engine.run("a").unwrap(), [SteelVal::IntV(3)]);
    assert_eq!(engine.run("b").unwrap(), [SteelVal::IntV(4)]);
}

#[test]
fn module_macro_templates_reference_native_definitions_past_local_shadows() {
    for kernel in [false, true] {
        // The kernel's `define-values` destructures a list.
        let producer = if kernel { "(list 42)" } else { "42" };
        let shadows: &[&str] = if kernel {
            &["(define (f x) (get-x))"]
        } else {
            &[
                "(define (f x) (get-x))",
                "(define (f y) (let ((x y)) (get-x)))",
            ]
        };
        for shadow in shadows {
            let mut engine = if kernel {
                Engine::new()
            } else {
                Engine::new_raw_no_kernel()
            };
            engine.register_steel_module(
                "native-globals".into(),
                format!(
                    "(provide answer)
                     (define-values (x) {producer})
                     (define-syntax get-x (syntax-rules () [(get-x) x]))
                     {shadow}
                     (define answer (f 7))"
                ),
            );
            assert_eq!(
                engine
                    .run("(require \"native-globals\") answer")
                    .unwrap_or_else(|error| panic!("kernel={kernel}, {shadow}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "kernel={kernel}, {shadow}"
            );
        }
    }
}

#[test]
fn raw_engine_macro_defined_values_export_from_modules() {
    let mut engine = Engine::new_raw_no_kernel();
    crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
    engine
        .run(
            r#"
        (require-builtin steel/lists)
        (define-syntax define-values
          (syntax-rules ()
            [(define-values (a b) expression)
             (begin (define temporary expression)
                    (define a (car temporary)) (define b (car (cdr temporary))))]))
    "#,
        )
        .unwrap();
    engine.register_steel_module(
        "values-module".into(),
        "(provide a b) (define-values (a b) '(3 4))".into(),
    );
    engine.run("(require \"values-module\")").unwrap();
    assert_eq!(engine.run("a").unwrap()[0], SteelVal::IntV(3));
    assert_eq!(engine.run("b").unwrap()[0], SteelVal::IntV(4));
}

#[test]
fn raw_engine_native_template_bindings_resolve_without_modules() {
    for (body, caller_binding) in [
        ("(define-values (x) 42) x", "x"),
        ("(begin (define-values (x) 42)) x", "x"),
        ("(define (read) x) (define-values (x) 42) (read)", "x"),
        ("(struct point (x)) (point-x (point 42))", "answer"),
        ("(begin (struct point (x))) (point-x (point 42))", "answer"),
        (
            "(struct point (x)) (if (point? (point 42)) (point-x (point 42)) 0)",
            "answer",
        ),
    ] {
        for template in [
            format!("(begin {body})"),
            format!("(let () {body})"),
            format!("((lambda () {body}))"),
        ] {
            let mut engine = Engine::new_raw_no_kernel();
            assert_eq!(
                engine
                    .run(format!(
                        "(define-syntax m (syntax-rules () [(m) {template}])) (m)"
                    ))
                    .unwrap_or_else(|error| panic!("{template}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(42)),
                "{template}"
            );
            assert_eq!(
                engine
                    .run(format!(
                        "(let (({caller_binding} 7) (point #f) (point? #f) (point-x #f))
                           (m) {caller_binding})"
                    ))
                    .unwrap_or_else(|error| panic!("{template}: {error}"))
                    .last(),
                Some(&SteelVal::IntV(7)),
                "{template}"
            );
        }
    }
}

#[test]
fn raw_engine_define_values_has_fresh_bindings_and_private_helpers() {
    let mut engine = Engine::new_raw_no_kernel();
    engine.run("(define-values (a b) '(1 2)) (define-values (c) 3) (define-values () '()) (define-values () '())").unwrap();
    for (name, expected) in [("a", 1), ("b", 2), ("c", 3)] {
        assert_eq!(engine.run(name).unwrap()[0], SteelVal::IntV(expected));
    }
    assert_eq!(engine.run("((lambda (producer #%values-destructure #%values-ref) (define-values (x y) producer) y) '(4 5) #f #f)").unwrap()[0], SteelVal::IntV(5));
    engine.run("(define (destructure producer #%values-destructure #%values-ref) (define-values (x y) producer) y)").unwrap();
    assert_eq!(
        engine.run("(destructure '(12 13) #f #f)").unwrap()[0],
        SteelVal::IntV(13)
    );
    engine.run("(define-syntax pair-definitions (syntax-rules () [(pair-definitions x y) (begin (define-values (x) 6) (define-values (y) 7))])) (pair-definitions d e)").unwrap();
    assert_eq!(engine.run("e").unwrap()[0], SteelVal::IntV(7));
    for source in [
        "(define-values (too few) '(1))",
        "(define-values (too-many) '(1 2))",
        "(define-values () '(1))",
        "(define-values (duplicate duplicate) '(1 2))",
        "(define-values (1) '(1))",
        "(define-values (a . b) '(1 2))",
        "(define-values name '(1))",
    ] {
        assert!(engine.run(source).is_err(), "{source}");
    }
}

#[test]
fn raw_engine_define_values_releases_temporary_payloads() {
    use std::sync::Arc;

    struct Probe(#[allow(dead_code)] Arc<()>);
    impl crate::rvals::Custom for Probe {}

    let count = Arc::new(());
    let factory = count.clone();
    let mut engine = Engine::new_raw_no_kernel();
    crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
    engine.run("(require-builtin steel/meta)").unwrap();
    engine.register_fn("probe-value", move || Probe(factory.clone()));
    for producer in ["(probe-value)", "(box (probe-value))"] {
        for _ in 0..3 {
            engine
                .run(format!("(define-values (payload) {producer})"))
                .unwrap();
            assert_eq!(Arc::strong_count(&count), 3);
            engine.run("(set! payload #f)").unwrap();
            engine.run("(#%gc-collect) (#%gc-collect)").unwrap();
            assert_eq!(Arc::strong_count(&count), 2, "{producer}");
        }
    }
}

#[test]
fn raw_engine_define_values_preserves_definitions_and_module_exports() {
    let mut engine = Engine::new_raw_no_kernel();
    crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
    engine
        .run("(require-builtin steel/numbers) (require-builtin steel/lists) (require-builtin steel/ord) (require-builtin steel/equality)")
        .unwrap();
    engine.run("(define count 0) (define-values (x y) (begin (set! count (+ count 1)) '(8 9))) (define-values (even?) (lambda (_) 77))").unwrap();
    assert_eq!(engine.run("count").unwrap()[0], SteelVal::IntV(1));
    assert_eq!(engine.run("(even? 2)").unwrap()[0], SteelVal::IntV(77));
    assert_eq!(engine.run("(let () (define-values (recur-even) (lambda (n) (if (= n 0) #t (recur-odd (- n 1))))) (define-values (recur-odd) (lambda (n) (if (= n 0) #f (recur-even (- n 1))))) (recur-odd 9))").unwrap()[0], SteelVal::BoolV(true));
    assert_eq!(engine.run("(let () (define trace 0) (define-values (a) (begin (set! trace (+ (* trace 10) 1)) 3)) (set! trace (+ (* trace 10) 2)) (define-values (b) (begin (set! trace (+ (* trace 10) 3)) a)) (define-values () (begin (set! trace (+ (* trace 10) 4)) '())) trace)").unwrap()[0], SteelVal::IntV(1234));
    assert_eq!(engine.run("((lambda (outer) (let () (define-values (recur-even) (lambda (n) (if (= n 0) outer (recur-odd (- n 1))))) (define-values (recur-odd) (lambda (n) (if (= n 0) #f (recur-even (- n 1))))) (recur-even 8))) #t)").unwrap()[0], SteelVal::BoolV(true));
    engine.register_steel_module("fresh-values".into(), "(provide left right) (define-values (left) 10) (define-values () '()) (define-values (right) 11)".into());
    engine.run("(require \"fresh-values\")").unwrap();
    assert_eq!(engine.run("left").unwrap()[0], SteelVal::IntV(10));
    assert_eq!(engine.run("right").unwrap()[0], SteelVal::IntV(11));
}
