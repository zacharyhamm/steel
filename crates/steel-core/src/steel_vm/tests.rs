#[cfg(test)]
mod call_cc_tests {
    use crate::steel_vm::engine::Engine;
    use crate::steel_vm::register_fn::RegisterFn;

    #[test]
    fn test_async() {
        async fn test_function() -> usize {
            10 + await_within().await
        }

        async fn await_within() -> usize {
            25
        }

        let mut vm = Engine::new();

        // You can even register async finctions
        vm.register_fn("test", test_function);

        let contents = r#"
        ; *thread-queue* : list[continuation]
        (define *thread-queue* '())

        ; halt : continuation
        (define halt #f)

        ; current-continuation : -> continuation
        (define (current-continuation)
            (call/cc
                (lambda (cc)
                    (cc cc))))

        ; await : future -> value
        ; yield the current thread and loop until the value is completed
        (define (await future)
            (define output (poll! future))
            (if output
                output
                (begin
                    (yield)
                    (await future))))

        ; spawn : (-> anything) -> void
        (define (spawn thunk)
        (let ((cc (current-continuation)))
            (if (continuation? cc)
                (set! *thread-queue* (append *thread-queue* (list cc)))
                (begin
                    (thunk)
                    (quit)))))

        ; yield : value -> void
        (define (yield)
        (let ((cc (current-continuation)))
            (if (and (continuation? cc) (pair? *thread-queue*))
                (let ((next-thread (car *thread-queue*)))
                (set! *thread-queue* (append (cdr *thread-queue*) (list cc)))
                (next-thread 'resume))
                void)))

        ; quit : -> ...
        (define (quit)
        (if (pair? *thread-queue*)
            (let ((next-thread (car *thread-queue*)))
                (set! *thread-queue* (cdr *thread-queue*))
                (next-thread 'resume))
            (halt)))

        ; start-threads : -> ...
        (define (start-threads)
        (let ((cc (current-continuation)))
            (if cc
                (begin
                (set! halt (lambda () (cc #f)))
                (if (null? *thread-queue*)
                    void
                    (begin
                        (let ((next-thread (car *thread-queue*)))
                        (set! *thread-queue* (cdr *thread-queue*))
                        (next-thread 'resume)))))
                void)))


        ;; Example cooperatively threaded program
        (define counter 10)

        (define (make-thread-thunk name)
        (define (loop)
                (when (< counter 0)
                    (quit))
                (display "in thread ")
                (display name)
                (display "; counter = ")
                (display counter)
                (newline)
                (set! counter (- counter 1))
                (define output (await (test))) ;; block the execution of this thread on this future
                (display "Future done!: ")
                (display output)
                (newline)
                (yield)
                (loop))
        loop)

        (spawn (make-thread-thunk 'a))
        (spawn (make-thread-thunk 'b))
        (spawn (make-thread-thunk 'c))

        (start-threads)
        "#;

        vm.compile_and_run_raw_program(contents).unwrap();

        assert_eq!(vm.extract::<isize>("counter").unwrap(), -1);
    }
}

#[cfg(test)]
mod register_fn_tests {
    use crate::steel_vm::engine::Engine;
    use crate::steel_vm::register_fn::RegisterFn;

    fn external_function(arg1: usize, arg2: usize) -> usize {
        arg1 + arg2
    }

    fn option_function(arg1: Option<String>) -> Option<String> {
        arg1
    }

    fn result_function(arg1: Option<String>) -> Result<String, String> {
        if let Some(inner) = arg1 {
            Ok(inner)
        } else {
            Err("Got a none".to_string())
        }
    }

    fn add_one(arg: usize) -> usize {
        arg + 1
    }

    fn always_true(_arg: usize) -> bool {
        true
    }

    fn empty_function() {}

    #[test]
    fn test_register_fn() {
        let mut vm = Engine::new();

        // Here we can register functions
        // Any function can accept parameters that implement `FromSteelVal` and
        // return values that implement `IntoSteelVal`
        vm.register_fn("external-function", external_function);

        // See the docs for more information about `FromSteelVal` and `IntoSteelVal`
        // but we can see even functions that accept/return Option<T> or Result<T,E>
        // can be registered
        vm.register_fn("option-function", option_function);

        // Result values will map directly to errors in the VM and bubble back up
        vm.register_fn("result-function", result_function);

        // functions that return () return void
        vm.register_fn("empty-function", empty_function);

        vm.register_fn("adding-one", add_one);
        vm.register_fn("always-true", always_true);

        vm.compile_and_run_raw_program(
            r#"
        (define foo (external-function 10 25))
        (define bar (option-function "applesauce"))
        (define baz (result-function "bananas"))
        (define res (transduce (range 0 10)
                               (taking 5)
                               (into-reducer external-function 0)))
        (assert! (equal? (map adding-one '(0 1 2 3)) '(1 2 3 4)))
        (assert! (equal? (filter always-true '(0 1 2 3)) '(0 1 2 3)))
        (empty-function)
    "#,
        )
        .unwrap();

        let foo = vm.extract::<usize>("foo").unwrap();
        assert_eq!(35, foo);

        // Can also extract a value by specifying the type on the variable
        let bar: String = vm.extract("bar").unwrap();
        assert_eq!("applesauce".to_string(), bar);

        let baz: String = vm.extract("baz").unwrap();
        assert_eq!("bananas".to_string(), baz);

        let res: usize = vm.extract("res").unwrap();
        assert_eq!(10, res);
    }
}

#[cfg(test)]
mod register_type_tests {
    use crate::steel_vm::engine::Engine;
    use crate::steel_vm::register_fn::RegisterFn;

    // In order to register a type with Steel,
    // it must implement Clone, Debug, and Steel
    #[derive(Clone, Debug, PartialEq)]
    pub struct ExternalStruct {
        foo: usize,
        bar: String,
        baz: f64,
    }

    impl crate::rvals::Custom for ExternalStruct {}

    impl ExternalStruct {
        pub fn new(foo: usize, bar: String, baz: f64) -> Self {
            ExternalStruct { foo, bar, baz }
        }

        // Embedding functions that take self must take by value
        pub fn method_by_value(self) -> usize {
            self.foo
        }

        // Setters should update the value and return a new instance (functional set)
        pub fn set_foo(mut self, foo: usize) -> Self {
            self.foo = foo;
            self
        }
    }
    #[test]
    fn register_type_test() {
        let mut vm = Engine::new();

        // Registering a type gives access to a predicate for the type
        vm.register_type::<ExternalStruct>("ExternalStruct?");

        // Structs in steel typically have a constructor that is the name of the struct
        vm.register_fn("ExternalStruct", ExternalStruct::new);

        // register_fn can be chained
        vm.register_fn("method-by-value", ExternalStruct::method_by_value)
            .register_fn("set-foo", ExternalStruct::set_foo);

        let external_struct = ExternalStruct::new(1, "foo".to_string(), 12.4);

        // Registering an external value is fallible if the conversion fails for some reason
        // For instance, registering an Err(T) is fallible. However, most implementation outside of manual
        // ones should not fail
        vm.register_external_value("external-struct", external_struct)
            .unwrap();

        let _ = vm
            .compile_and_run_raw_program(
                r#"
            (define new-external-struct (set-foo external-struct 100))
            (define get-output (method-by-value external-struct))
            (define second-new-external-struct (ExternalStruct 50 "bananas" 72.6))
            "last-result"
        "#,
            )
            .unwrap();

        let new_external_struct = vm.extract::<ExternalStruct>("new-external-struct").unwrap();
        assert_eq!(
            ExternalStruct::new(100, "foo".to_string(), 12.4),
            new_external_struct
        );

        // Can also extract a value by specifying the type on the variable
        let get_output: usize = vm.extract("get-output").unwrap();
        assert_eq!(1, get_output);

        let second_new_external_struct: ExternalStruct =
            vm.extract("second-new-external-struct").unwrap();
        assert_eq!(
            ExternalStruct::new(50, "bananas".to_string(), 72.6),
            second_new_external_struct
        );
    }
}

#[cfg(test)]
mod contract_tests {
    use crate::steel_vm::test_util::{assert_script, assert_script_error};

    #[test]
    fn simple_flat_contract() {
        let script = r#"
          (define/contract (test x y)
            (->/c even? even? odd?)
            (+ x y 1))

          (assert! (equal? (test 2 2) 5))
        "#;
        assert_script(script);
    }

    #[test]
    fn simple_flat_contract_domain_violation() {
        let script = r#"
          (define/contract (test x y)
            (->/c even? even? odd?)
            (+ x y 1))

          (test 1 2)
        "#;
        assert_script_error(script);
    }

    #[test]
    fn simple_higher_order_contract() {
        let script = r#"
          (define/contract (blagh func y)
            (->/c (->/c even? odd?) even? even?)
            (+ 1 (func y)))

          (assert! (equal? (blagh (lambda (x) (+ x 1)) 2) 4))
        "#;
        assert_script(script);
    }

    #[test]
    fn simple_higher_order_contract_violation() {
        let script = r#"
          (define/contract (blagh func y)
            (->/c (->/c even? odd?) even? even?)
            (+ 1 (func y)))

          (blagh (lambda (x) (+ x 2)) 2)
        "#;
        assert_script_error(script);
    }

    // TODO: This will fail on old contract implementation
    // #[test]
    // fn tail_call_mutual_recursion() {
    //     let script = r#"
    //     (define/contract (foo x)
    //       (->/c int? int?)
    //         (if (= x 100)
    //             x
    //             (bar (+ x 1))))

    //     (define/contract (bar x)
    //       (->/c int? int?)
    //         (if (= x 100)
    //             x
    //             (foo (+ x 1))))

    //     (assert! (equal? (foo 0) 100))
    //   "#;
    //     assert_script(script);
    // }

    #[test]
    fn tail_call_contract_still_works() {
        let script = r#"
          (define/contract (loop x)
            (->/c int? int?)
              (if (= x 100)
                  x
                  (loop (+ x 1))))

          (assert! (equal? (loop 0) 100))
        "#;
        assert_script(script);
    }

    #[test]
    fn contract_checking_on_application_success() {
        let script = r#"

        (define/contract (output)
            (->/c (->/c string? int?))
            (lambda (x) 10))

        (define/contract (accept func)
            (->/c (->/c string? int?) string?)
            "cool cool cool")

        (assert! (equal? (accept (output)) "cool cool cool"))
        "#;
        assert_script(script);
    }

    #[test]
    fn contract_checking_not_called_since_not_applied() {
        let script = r#"

        (define/contract (output)
            (->/c (->/c string? int?))
            (lambda (x) 10))

        (define/contract (accept func)
            (->/c (->/c string? string?) string?)
            "cool cool cool")

        (assert! (equal? (accept (output)) "cool cool cool"))
        "#;
        assert_script(script);
    }

    #[test]
    fn contract_checking_on_return_does_not_happen() {
        let script = r#"

        (define/contract (output)
            (->/c (->/c string? int?))
            (lambda (x) 10))

        (define/contract (accept)
            (->/c (->/c string? string?))
            (output))

        (accept)
        "#;

        assert_script(script);
    }

    #[test]
    fn contract_application_in_map() {
        let script = r#"
        (define (test x)
            (->/c int? int?)
            (+ x 1))
        (define result (map test (list 1 2 3 4)))
        (assert! (equal? result (list 2 3 4 5)))
        "#;
        assert_script(script);
    }

    #[test]
    fn contract_application_in_filter() {
        let script = r#"
        (define (test x)
            (->/c int? boolean?)
            (even? x))
        (define result (filter test (list 1 2 3 4)))
        (assert! (equal? result (list 2 4)))
        "#;
        assert_script(script);
    }

    #[test]
    fn contract_checking_with_weaker() {
        let script = r#"
        (define/contract (output)
            (->/c (->/c string? int?))
            (lambda (x) 10.1))

        (define/contract (accept)
            (->/c (->/c string? number?))
            (output))

        ((accept) "test")
        "#;

        assert_script_error(script)
    }

    #[test]
    fn contract_checking_pre_condition_later() {
        let script = r#"
        (define/contract (output)
            (->/c (->/c list? int?))
            (lambda (x) 10.0))

        (define/contract (accept)
            (->/c (->/c string? number?))
            (output))

        ((accept) "test")
        "#;

        assert_script_error(script);
    }

    #[test]
    fn three_levels_of_contracts() {
        let script = r#"
        (define (any? x) #t)

        (define/contract (level1)
            (->/c (->/c int?))
            (lambda () 10.2))

        (define/contract (level2)
            (->/c (->/c number?))
            (level1))

        (define/contract (level3)
            (->/c (->/c any?))
            (level2))

        ((level3))
        "#;

        assert_script_error(script);
    }

    #[test]
    fn contract_with_filter() {
        let script = r#"
        (define/contract (is-even? x)
            (->/c number? boolean?)
            (even? x))

        (define res (filter is-even? (range 0 10)))

        (assert! (equal? res '(0 2 4 6 8)))
        "#;

        assert_script(script);
    }

    #[test]
    fn contract_with_map() {
        let script = r#"
        (define/contract (adding1 x)
            (->/c number? number?)
            (+ x 1))

        (define res (map adding1 (range 0 5)))

        (assert! (equal? res '(1 2 3 4 5)))
        "#;

        assert_script(script);
    }

    #[test]
    fn contract_with_reduce() {
        let script = r#"
        (define/contract (reducer accum elem)
            (->/c number? number? number?)
            (+ accum elem))

        (define res (transduce (range 0 10) (taking 5) (into-reducer + 0)))

        (assert! (equal? res 10))
        "#;
        assert_script(script);
    }

    #[test]
    fn transducers_containing_contracts() {
        let script = r#"
        (define/contract (mapper x)
            (->/c number? number?)
            (+ x 1))

        (define/contract (is-even? x)
            (->/c number? boolean?)
            (even? x))

        (define x (mapping mapper))
        (define y (filtering is-even?))
        (define z (taking 10))

        (define xyz (compose x y z))

        (define exec-list (transduce (range 0 100) xyz (into-list)))
        (define exec-vector (transduce (range 0 100) xyz (into-vector)))
        (define my-sum (transduce (range 0 100) xyz (into-reducer + 0)))

        (assert! (equal? exec-list '(2 4 6 8 10 12 14 16 18 20)))
        (assert! (equal? exec-vector (vector 2 4 6 8 10 12 14 16 18 20)))
        (assert! (equal? my-sum 110))
        "#;
        assert_script(script);
    }
}

#[cfg(test)]
mod find_closest_match_tests {
    use crate::steel_vm::builtin::find_closest_match;

    #[test]
    fn similar_candidate_returns_similiar_candidate() {
        assert_eq!(
            find_closest_match("make-struct", ["unrelated", "--make-struct"]),
            Some("--make-struct")
        );
    }

    #[test]
    fn no_similar_strings_returns_none() {
        assert_eq!(
            find_closest_match("make-struct", ["unrelated", "make-tuple"]),
            None
        );
    }

    #[test]
    fn multiple_similar_strings_returns_most_similar() {
        assert_eq!(
            find_closest_match(
                "make-struct",
                ["unrelated", "--make-struct", "--make-stract"]
            ),
            Some("--make-struct")
        );
    }
}

#[cfg(test)]
mod exported_macro_quote_tests {
    use crate::steel_vm::engine::Engine;

    #[test]
    fn quoted_names_in_exported_macros() {
        let mut engine = Engine::new();
        engine.register_steel_module(
            "quoting-macros".to_string(),
            "(provide tick long-quote quoted-list quasi nested)
             (define (helper x) x)
             (define counter 10)
             (define-syntax tick (syntax-rules () [(_) 'helper]))
             (define-syntax long-quote (syntax-rules () [(_) (quote helper)]))
             (define-syntax quoted-list (syntax-rules () [(_) (quote (helper counter))]))
             (define-syntax quasi
               (syntax-rules () [(_) `(helper ,counter ,@(list (helper 3)))]))
             (define-syntax nested
               (syntax-rules () [(_) `(helper `(counter ,(counter ,counter)))]))"
                .to_string(),
        );
        let values = engine
            .compile_and_run_raw_program(
                "(require \"quoting-macros\")
                 (list (tick) (long-quote) (quoted-list) (quasi) (nested))",
            )
            .unwrap();
        assert_eq!(
            values.last().unwrap().to_string(),
            "(helper helper (helper counter) (helper 10 3) \
             (helper (quasiquote (counter (unquote (counter 10))))))"
        );
    }
}

#[cfg(test)]
fn gc_collect(engine: &mut crate::steel_vm::engine::Engine) {
    engine.run("(#%gc-collect)").unwrap();
}

// TODO: We should be able to simplify this a lot, but this is an annoying way to
// make sure that we don't block on blocking FFI calls.
//
// in memory blocking calls are also victim to this, but less so, because you can
// pass immutable references to them, whereas all dylib calls are mutably referenced
// by default.
#[cfg(all(test, feature = "sync", feature = "dylibs"))]
mod ffi_borrowed_custom_value_tests {
    use crate::rvals::SteelVal;
    use crate::steel_vm::engine::Engine;
    use crate::steel_vm::ffi::{FFIModule, RegisterFFIFn};
    use crate::steel_vm::tests::gc_collect;
    use abi_stable::std_types::RBox;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::mpsc::channel;
    use std::time::Duration;

    static STARTED: AtomicBool = AtomicBool::new(false);
    static RELEASE: AtomicBool = AtomicBool::new(false);

    struct Blocker;

    impl crate::rvals::Custom for Blocker {}

    impl Blocker {
        fn wait(&mut self) {
            STARTED.store(true, Ordering::SeqCst);
            while !RELEASE.load(Ordering::SeqCst) {
                std::thread::sleep(Duration::from_millis(1));
            }
        }
    }

    #[test]
    fn collection_finishes_while_dylib_call_holds_its_argument() {
        let (done_tx, done_rx) = channel();

        std::thread::spawn(move || {
            let mut module = FFIModule::new("test/blocker");
            module
                .register_fn("make-blocker", || Blocker)
                .register_fn("blocker-wait!", Blocker::wait);

            let mut engine = Engine::new();
            engine.register_external_module(RBox::new(module)).unwrap();
            engine
                .run("(require-builtin test/blocker) (define blocker (make-blocker))")
                .unwrap();

            let blocker = engine.extract_value("blocker").unwrap();
            let SteelVal::BoxedFunction(wait) = engine.extract_value("blocker-wait!").unwrap()
            else {
                panic!("expected a boxed function");
            };

            let caller = std::thread::spawn(move || wait.func()(&[blocker]).unwrap());
            while !STARTED.load(Ordering::SeqCst) {
                std::thread::yield_now();
            }

            gc_collect(&mut engine);
            done_tx.send(()).unwrap();

            RELEASE.store(true, Ordering::SeqCst);
            caller.join().unwrap();
        });

        let finished = done_rx.recv_timeout(Duration::from_secs(20));
        RELEASE.store(true, Ordering::SeqCst);
        finished.expect("collection blocked on a value borrowed by a dylib call");
    }
}

#[cfg(all(test, feature = "sync", feature = "dylibs"))]
mod ffi_shared_receiver_tests {
    use crate::gc::shared::ShareableMut;
    use crate::rvals::{AsRefMutSteelVal, SteelVal};
    use crate::steel_vm::engine::Engine;
    use crate::steel_vm::ffi::{
        AsRefFFIVal, FFIArg, FFIBoxedDynFunction, FFIModule, FFIValue, FFIWrappedModule,
        HostRuntimeFunction, IntoFFIVal, RFn_TO, RegisterFFIFn, SHARED_RECEIVER,
    };
    use crate::steel_vm::tests::gc_collect;
    use abi_stable::sabi_trait::TD_CanDowncast;
    use abi_stable::std_types::{RArc, RBox, RBoxError, RResult, RSliceMut, RString};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::mpsc::{channel, RecvTimeoutError};
    use std::thread::JoinHandle;
    use std::time::Duration;

    struct Counter(AtomicUsize);

    impl crate::rvals::Custom for Counter {}

    impl Counter {
        fn get(&self) -> usize {
            self.0.load(Ordering::SeqCst)
        }

        fn add(&self, n: usize) -> usize {
            self.0.fetch_add(n, Ordering::SeqCst) + n
        }

        fn reset(&mut self) {
            *self.0.get_mut() = 0;
        }
    }

    fn counter_getter() -> FFIValue {
        let function = |args: RSliceMut<'static, FFIArg<'static>>| -> RResult<FFIValue, RBoxError> {
            let mut args = args.into_iter();
            match <Counter as AsRefFFIVal>::as_ref(args.next().unwrap()) {
                RResult::ROk(counter) => counter.get().into_ffi_val(),
                RResult::RErr(e) => RResult::RErr(e),
            }
        };

        FFIValue::BoxedFunction(RBox::new(FFIBoxedDynFunction {
            name: RString::from("counter-get"),
            arity: SHARED_RECEIVER,
            function: RFn_TO::from_ptr(RArc::new(function), TD_CanDowncast),
        }))
    }

    static EXCLUSIVE_STARTED: AtomicBool = AtomicBool::new(false);
    static EXCLUSIVE_RELEASE: AtomicBool = AtomicBool::new(false);

    #[derive(Default)]
    struct Blocker {
        started: AtomicBool,
        release: AtomicBool,
    }

    impl crate::rvals::Custom for Blocker {}

    impl Blocker {
        fn wait(&self) {
            self.started.store(true, Ordering::SeqCst);
            while !self.release.load(Ordering::SeqCst) {
                std::thread::sleep(Duration::from_millis(1));
            }
        }

        fn started(&self) -> bool {
            self.started.load(Ordering::SeqCst)
        }

        fn release(&self) {
            self.release.store(true, Ordering::SeqCst);
        }

        fn ping(&self) -> bool {
            true
        }

        fn poke(&mut self) -> bool {
            true
        }

        fn wait_exclusive(&mut self) {
            EXCLUSIVE_STARTED.store(true, Ordering::SeqCst);
            while !EXCLUSIVE_RELEASE.load(Ordering::SeqCst) {
                std::thread::sleep(Duration::from_millis(1));
            }
        }

        fn call_with(&self, function: HostRuntimeFunction) -> bool {
            function.call(RSliceMut::from_mut_slice(&mut [])).is_ok()
        }
    }

    struct HostOnly;

    impl crate::rvals::Custom for HostOnly {}

    fn module() -> RBox<FFIModule> {
        let mut module = FFIModule::new("test/shared");
        module
            .register_fn("make-counter", || Counter(AtomicUsize::new(0)))
            .register_fn("counter-get", Counter::get)
            .register_fn("counter-add!", Counter::add)
            .register_fn("counter-reset!", Counter::reset)
            .register_fn("counter-getter", counter_getter)
            .register_fn("make-blocker", Blocker::default)
            .register_fn("blocker-wait", Blocker::wait)
            .register_fn("blocker-started?", Blocker::started)
            .register_fn("blocker-release!", Blocker::release)
            .register_fn("blocker-ping", Blocker::ping)
            .register_fn("blocker-poke!", Blocker::poke)
            .register_fn("blocker-wait-exclusive!", Blocker::wait_exclusive)
            .register_fn("blocker-call-with", Blocker::call_with);

        RBox::new(module)
    }

    fn engine() -> Engine {
        let mut engine = Engine::new();
        engine.register_external_module(module()).unwrap();
        engine.run("(require-builtin test/shared)").unwrap();
        engine
    }

    fn engine_with_old_module() -> Engine {
        let module = FFIWrappedModule::new(module(), Some(usize::MAX))
            .unwrap()
            .build();

        let mut engine = Engine::new();
        engine.register_module(module);
        engine.run("(require-builtin test/shared)").unwrap();
        engine
    }

    fn boxed(engine: &mut Engine, name: &str) -> SteelVal {
        engine.extract_value(name).unwrap()
    }

    fn call(function: &SteelVal, args: &[SteelVal]) -> crate::rvals::Result<SteelVal> {
        let SteelVal::BoxedFunction(function) = function else {
            panic!("expected a boxed function");
        };
        function.func()(args)
    }

    fn call_on(engine: &mut Engine, name: &str, value: &SteelVal) -> bool {
        call(&boxed(engine, name), &[value.clone()]).is_ok()
    }

    fn spawn_call_on(engine: &mut Engine, name: &str, value: &SteelVal) -> JoinHandle<bool> {
        let function = boxed(engine, name);
        let value = value.clone();
        std::thread::spawn(move || call(&function, &[value]).is_ok())
    }

    fn eval(engine: &mut Engine, expr: &str) -> SteelVal {
        engine.run(expr.to_string()).unwrap().pop().unwrap()
    }

    fn with_timeout<T: Send + 'static>(test: impl FnOnce() -> T + Send + 'static) -> T {
        let (done_tx, done_rx) = channel();
        std::thread::spawn(move || done_tx.send(test()).unwrap());
        match done_rx.recv_timeout(Duration::from_secs(20)) {
            Ok(result) => result,
            Err(RecvTimeoutError::Timeout) => {
                panic!("blocked on a value borrowed over the ffi boundary")
            }
            Err(RecvTimeoutError::Disconnected) => panic!("the test thread panicked"),
        }
    }

    fn wait_until(condition: impl Fn() -> bool) {
        while !condition() {
            // Yielding let this test be more predictable than sleeping for a ms
            // for some reason
            std::thread::yield_now();
        }
    }

    fn count_errors(
        threads: usize,
        iterations: usize,
        f: impl Fn(usize) -> crate::rvals::Result<SteelVal> + Sync,
    ) -> usize {
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .map(|index| {
                    let f = &f;
                    scope.spawn(move || (0..iterations).filter(|_| f(index).is_err()).count())
                })
                .collect();

            handles.into_iter().map(|x| x.join().unwrap()).sum()
        })
    }

    fn hammer(mut engine: Engine, get: SteelVal) {
        let counter = eval(&mut engine, "(make-counter)");
        let add = boxed(&mut engine, "counter-add!");

        let errors = count_errors(4, 50_000, |_| {
            call(&add, &[counter.clone(), SteelVal::IntV(1)])?;
            call(&get, &[counter.clone()])
        });

        assert_eq!(errors, 0);
        assert_eq!(call(&get, &[counter]).unwrap(), SteelVal::IntV(200_000));
    }

    fn make_blocker(engine: &mut Engine) -> SteelVal {
        engine.run("(define blocker (make-blocker))").unwrap();
        boxed(engine, "blocker")
    }

    fn hold_shared(engine: &mut Engine, blocker: &SteelVal) -> JoinHandle<bool> {
        let holder = spawn_call_on(engine, "blocker-wait", blocker);
        let started = boxed(engine, "blocker-started?");
        wait_until(|| call(&started, &[blocker.clone()]).unwrap() == SteelVal::BoolV(true));
        holder
    }

    fn wait_for_queued_writer(blocker: &SteelVal) {
        let SteelVal::Custom(lock) = blocker else {
            panic!("expected a custom value");
        };
        wait_until(|| lock.try_read().is_err());
    }

    #[test]
    fn threads_share_a_value_through_ref_methods() {
        let mut engine = engine();
        let get = boxed(&mut engine, "counter-get");
        hammer(engine, get);
    }

    #[test]
    fn threads_share_a_value_through_the_old_module_loader() {
        let mut engine = engine_with_old_module();
        let get = boxed(&mut engine, "counter-get");
        hammer(engine, get);
    }

    #[test]
    fn threads_share_a_value_through_a_returned_function() {
        let mut engine = engine();
        let get = eval(&mut engine, "(counter-getter)");
        hammer(engine, get);
    }

    #[test]
    fn the_flag_does_not_show_in_the_arity() {
        let mut engine = engine();
        let get = boxed(&mut engine, "counter-get");
        let returned = eval(&mut engine, "(counter-getter)");

        for function in [get, returned] {
            let SteelVal::BoxedFunction(function) = function else {
                panic!("expected a boxed function");
            };
            assert_eq!(function.get_arity(), Some(0));
        }

        let FFIValue::BoxedFunction(function) = counter_getter() else {
            unreachable!()
        };
        assert_eq!(format!("{:?}", function), "#<counter-get:0>");
    }

    #[test]
    fn a_by_value_argument_still_borrows_exclusively() {
        let mut engine = engine();
        engine.run("(define c (make-counter))").unwrap();

        let error = engine.run("(counter-add! c c)").unwrap_err().to_string();
        assert!(error.contains("borrowed"), "{}", error);

        engine.run("(counter-reset! c)").unwrap();
        assert_eq!(eval(&mut engine, "(counter-get c)"), SteelVal::IntV(0));
    }

    #[test]
    fn readers_and_writers_on_one_value_never_fail() {
        let mut engine = engine();
        let counter = eval(&mut engine, "(make-counter)");
        let get = boxed(&mut engine, "counter-get");
        let add = boxed(&mut engine, "counter-add!");
        let reset = boxed(&mut engine, "counter-reset!");

        let errors = count_errors(5, 20_000, |index| match index {
            0 => call(&reset, &[counter.clone()]),
            1 => call(&add, &[counter.clone(), SteelVal::IntV(1)]),
            _ => call(&get, &[counter.clone()]),
        });

        assert_eq!(errors, 0);
    }

    #[test]
    fn an_exclusive_borrow_waits_for_shared_ones() {
        let result = with_timeout(|| {
            let mut engine = engine();
            let blocker = make_blocker(&mut engine);
            let reader = hold_shared(&mut engine, &blocker);
            let writer = spawn_call_on(&mut engine, "blocker-poke!", &blocker);
            wait_for_queued_writer(&blocker);

            let shared = call_on(&mut engine, "blocker-ping", &blocker);
            gc_collect(&mut engine);
            let early = writer.is_finished();

            call_on(&mut engine, "blocker-release!", &blocker);
            reader.join().unwrap();

            (shared, early, writer.join().unwrap())
        });

        assert_eq!(result, (true, false, true));
    }

    #[test]
    fn a_shared_borrow_waits_for_an_exclusive_one() {
        let result = with_timeout(|| {
            let mut engine = engine();
            let blocker = make_blocker(&mut engine);
            let writer = spawn_call_on(&mut engine, "blocker-wait-exclusive!", &blocker);
            wait_until(|| EXCLUSIVE_STARTED.load(Ordering::SeqCst));
            let reader = spawn_call_on(&mut engine, "blocker-ping", &blocker);

            std::thread::sleep(Duration::from_millis(100));
            gc_collect(&mut engine);
            let early = reader.is_finished();

            EXCLUSIVE_RELEASE.store(true, Ordering::SeqCst);
            writer.join().unwrap();

            (early, reader.join().unwrap())
        });

        assert_eq!(result, (false, true));
    }

    #[test]
    fn a_waiting_writer_does_not_block_shared_borrows() {
        let result = with_timeout(|| {
            let mut engine = engine();
            let blocker = make_blocker(&mut engine);
            let reader = hold_shared(&mut engine, &blocker);
            let writer = {
                let blocker = blocker.clone();
                std::thread::spawn(move || {
                    <HostOnly as AsRefMutSteelVal>::as_mut_ref(&blocker).is_ok()
                })
            };
            wait_for_queued_writer(&blocker);

            let shared = call_on(&mut engine, "blocker-ping", &blocker);
            gc_collect(&mut engine);

            call_on(&mut engine, "blocker-release!", &blocker);
            reader.join().unwrap();

            (shared, writer.join().unwrap())
        });

        assert_eq!(result, (true, false));
    }

    #[test]
    fn a_borrowed_value_can_reenter_through_the_host() {
        let result = with_timeout(|| {
            let mut engine = engine();
            eval(
                &mut engine,
                "(require-builtin steel/ffi)
                 (define b (make-blocker))
                 (list (blocker-call-with b (function->ffi-function (lambda () (blocker-ping b))))
                       (blocker-call-with b (function->ffi-function (lambda () (blocker-poke! b))))
                       (blocker-poke! b))",
            )
            .to_string()
        });

        assert_eq!(result, "(#true #false #true)");
    }
}

#[cfg(test)]
mod source_gc_tests {
    use crate::steel_vm::{builtin::BuiltInModule, engine::Engine, register_fn::RegisterFn};

    #[test]
    fn required_module_survives_sources_gc() {
        let mut engine = Engine::new();
        let mut module = BuiltInModule::new("#%test/builtin");
        module.register_fn("one", || 1);
        engine.register_module(module);
        engine.register_steel_module(
            "reexport".to_string(),
            "(require-builtin #%test/builtin) (provide one)".to_string(),
        );
        let program = format!("(require \"reexport\")\n;{}", "x".repeat(1 << 20));
        for _ in 0..10 {
            engine.compile_and_run_raw_program(program.clone()).unwrap();
        }
    }
}

#[cfg(test)]
mod embedding_regressions {
    use crate::steel_vm::engine::Engine;

    #[test]
    fn replacing_struct_properties_releases_embedded_engine() {
        use crate::{rvals::IntoSteelVal, steel_vm::register_fn::RegisterFn};
        use std::{
            process::Command,
            sync::{
                atomic::{AtomicUsize, Ordering},
                Arc,
            },
            time::{Duration, Instant},
        };

        const CHILD: &str = "STEEL_PROPERTY_REPLACEMENT_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let mut child = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "steel_vm::tests::embedding_regressions::replacing_struct_properties_releases_embedded_engine", "--nocapture"])
                .env(CHILD, "1")
                .spawn()
                .unwrap();
            let deadline = Instant::now() + Duration::from_secs(30);
            loop {
                if let Some(status) = child.try_wait().unwrap() {
                    assert!(
                        status.success(),
                        "property replacement child failed: {status}"
                    );
                    return;
                }
                if Instant::now() >= deadline {
                    child.kill().unwrap();
                    child.wait().unwrap();
                    panic!("property replacement deadlocked");
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }

        struct EmbeddedEngine {
            _engine: Engine,
            dropped: Arc<AtomicUsize>,
        }
        impl crate::rvals::Custom for EmbeddedEngine {}
        impl Drop for EmbeddedEngine {
            fn drop(&mut self) {
                self.dropped.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut embedded = Engine::new_raw_no_kernel();
        let stored_drops = store_thread_clone(&mut embedded, false);
        let heap = Arc::downgrade(&embedded.virtual_machine.heap);
        let dropped = Arc::new(AtomicUsize::new(0));
        let value = EmbeddedEngine {
            _engine: embedded,
            dropped: dropped.clone(),
        }
        .into_steelval()
        .unwrap();
        let mut engine = Engine::new();
        engine.register_fn(
            "#%vtable-update-entry!",
            crate::values::structs::VTable::set_entry,
        );
        engine.run("(struct holder ())").unwrap();
        engine.register_value("embedded", value);
        engine.run("(#%vtable-update-entry! struct:holder #f (hash '#:owner embedded)) (set! embedded #f)").unwrap();
        assert_eq!(dropped.load(Ordering::SeqCst), 0);
        engine
            .run("(#%vtable-update-entry! struct:holder #f (hash))")
            .unwrap();
        assert_eq!(dropped.load(Ordering::SeqCst), 1);
        assert_eq!(stored_drops.load(Ordering::SeqCst), 1);
        assert!(heap.upgrade().is_none());
    }

    #[cfg(feature = "sync")]
    #[test]
    fn exported_boxed_callback_keeps_globals_alive_after_engine_drop() {
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine.register_value(
            "#%closure->boxed-function",
            crate::SteelVal::BuiltIn(crate::steel_vm::primitives::closure_to_boxed_function),
        );
        let heap = std::sync::Arc::downgrade(&engine.virtual_machine.heap);
        let callback = engine
            .run(
                "(require-builtin steel/meta)
                 (define state (box 42))
                 (#%closure->boxed-function (lambda () (unbox state)))",
            )
            .unwrap()
            .pop()
            .unwrap();
        let crate::SteelVal::BoxedFunction(callback) = callback else {
            panic!("expected a boxed callback");
        };
        drop(engine);
        for _ in 0..2 {
            assert_eq!(callback.func()(&[]).unwrap(), crate::SteelVal::IntV(42));
        }
        drop(callback);
        assert!(heap.upgrade().is_none());
    }

    #[cfg(all(feature = "sync", feature = "dylibs"))]
    #[test]
    fn exported_ffi_callback_keeps_globals_alive_after_engine_drop() {
        use crate::steel_vm::ffi::{FFIValue, HostRuntimeFunction};
        use abi_stable::std_types::RSliceMut;

        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine.register_value(
            "function->ffi-function",
            crate::SteelVal::BuiltIn(crate::steel_vm::ffi::function_to_ffi_function),
        );
        let heap = std::sync::Arc::downgrade(&engine.virtual_machine.heap);
        let callback = engine
            .run(
                "(require-builtin steel/meta)
                 (define state (box 42))
                 (function->ffi-function (lambda () (unbox state)))",
            )
            .unwrap()
            .pop()
            .unwrap();
        let crate::SteelVal::Custom(callback) = callback else {
            panic!("expected an FFI callback");
        };
        drop(engine);
        {
            let guard = callback.read();
            let function =
                crate::rvals::as_underlying_type::<HostRuntimeFunction>(guard.as_ref()).unwrap();
            for _ in 0..2 {
                assert!(matches!(
                    function.call(RSliceMut::from_mut_slice(&mut [])).unwrap(),
                    FFIValue::IntV(42)
                ));
            }
        }
        drop(callback);
        assert!(heap.upgrade().is_none());
    }

    #[test]
    fn cloned_thread_keeps_globals_alive_after_engine_drop() {
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        let heap = std::sync::Arc::downgrade(&engine.virtual_machine.heap);
        let function = engine
            .run(
                "(require-builtin steel/meta)
                 (define state (box 42))
                 (lambda () (unbox state))",
            )
            .unwrap()
            .pop()
            .unwrap();
        let mut thread = engine.virtual_machine.clone();
        drop(engine);
        assert_eq!(
            thread.call_fn_from_mut_slice(function, &mut []).unwrap(),
            crate::SteelVal::IntV(42)
        );
        drop(thread);
        assert!(heap.upgrade().is_none());
    }

    struct StoredThread {
        _thread: crate::steel_vm::vm::SteelThread,
        dropped: std::sync::Arc<std::sync::atomic::AtomicUsize>,
        heap: std::sync::Weak<crate::steel_vm::vm::HeapState>,
    }

    impl crate::rvals::Custom for StoredThread {}

    impl Drop for StoredThread {
        fn drop(&mut self) {
            if let Some(heap) = self.heap.upgrade() {
                assert!(
                    heap.try_lock().is_some(),
                    "payload dropped under the heap lock"
                );
            }
            self.dropped
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
    }

    fn store_thread_clone(
        engine: &mut Engine,
        vector: bool,
    ) -> std::sync::Arc<std::sync::atomic::AtomicUsize> {
        use crate::rvals::IntoSteelVal;
        use std::sync::{atomic::AtomicUsize, Arc};

        let dropped = Arc::new(AtomicUsize::new(0));
        let stored = StoredThread {
            _thread: engine.virtual_machine.clone_for_storage(),
            dropped: dropped.clone(),
            heap: Arc::downgrade(&engine.virtual_machine.heap),
        }
        .into_steelval()
        .unwrap();
        let value = if vector {
            crate::SteelVal::MutableVector(
                engine
                    .virtual_machine
                    .heap
                    .lock()
                    .allocate_vec_without_collection(vec![stored]),
            )
        } else {
            crate::SteelVal::HeapAllocated(
                engine
                    .virtual_machine
                    .heap
                    .lock()
                    .allocate_without_collection(stored),
            )
        };
        engine.register_value("stored-thread", value);
        dropped
    }

    #[test]
    fn teardown_reclaims_heap_stored_vm_clones_after_the_last_engine() {
        use std::sync::{atomic::Ordering, Arc};

        for vector in [false, true] {
            let mut engine = Engine::new_raw_no_kernel();
            let heap = Arc::downgrade(&engine.virtual_machine.heap);
            let dropped = store_thread_clone(&mut engine, vector);
            let live = crate::SteelVal::HeapAllocated(
                engine
                    .virtual_machine
                    .heap
                    .lock()
                    .allocate_without_collection(crate::SteelVal::IntV(42)),
            );
            engine.register_value("live", live);
            let survivor = engine.clone();
            drop(engine);
            assert_eq!(dropped.load(Ordering::SeqCst), 0);
            assert_eq!(
                survivor.extract_value("live").unwrap().as_box_to_inner(),
                Some(crate::SteelVal::IntV(42))
            );
            drop(survivor);
            assert_eq!(dropped.load(Ordering::SeqCst), 1);
            assert!(heap.upgrade().is_none());
        }
    }

    #[test]
    fn deep_cloned_heaps_have_independent_execution_owners() {
        use std::sync::{atomic::Ordering, Arc};

        let mut original = Engine::new_raw_no_kernel();
        let cell = crate::SteelVal::HeapAllocated(
            original
                .virtual_machine
                .heap
                .lock()
                .allocate_without_collection(crate::SteelVal::IntV(7)),
        );
        original.register_value("cell", cell);
        let mut isolated = original.deep_clone();
        let (crate::SteelVal::HeapAllocated(original_cell), crate::SteelVal::HeapAllocated(copy)) = (
            original.extract_value("cell").unwrap(),
            isolated.extract_value("cell").unwrap(),
        ) else {
            panic!("expected heap cells");
        };
        assert!(!original_cell.ptr_eq(&copy));
        let original_heap = Arc::downgrade(&original.virtual_machine.heap);
        let isolated_heap = Arc::downgrade(&isolated.virtual_machine.heap);
        let original_drops = store_thread_clone(&mut original, false);
        let isolated_drops = store_thread_clone(&mut isolated, true);
        drop(original);
        assert_eq!(original_drops.load(Ordering::SeqCst), 1);
        assert!(original_heap.upgrade().is_none());
        assert_eq!(copy.get(), crate::SteelVal::IntV(7));
        assert_eq!(isolated_drops.load(Ordering::SeqCst), 0);
        assert!(isolated_heap.upgrade().is_some());
        drop(isolated);
        assert_eq!(isolated_drops.load(Ordering::SeqCst), 1);
        assert!(isolated_heap.upgrade().is_none());
    }

    #[test]
    fn deep_cloned_engines_do_not_share_heap_cells() {
        for drop_template_first in [true, false] {
            let mut template = Engine::new();
            register_gc(&mut template);
            template
                .run(
                    "(define b (box 1))
                     (define counter (let ((n 0)) (lambda () (set! n (+ n 1)) n)))
                     (define v (vector (box 10)))
                     (struct point (x) #:mutable)
                     (define p (point 1))
                     (define shared (list b v))",
                )
                .unwrap();
            let mut copy = template.deep_clone();
            copy.run("(set-box! b 2) (counter) (set-box! (vector-ref v 0) 20) (set-point-x! p 5)")
                .unwrap();
            let (mut survivor, expected) = if drop_template_first {
                drop(template);
                (copy, "(2 2 20 5 #true #true)")
            } else {
                drop(copy);
                (template, "(1 1 10 1 #true #true)")
            };
            survivor.run("(probe-gc) (probe-gc)").unwrap();
            let read = survivor
                .run(
                    "(list (unbox b) (counter) (unbox (vector-ref v 0)) (point-x p)
                           (eq? (car shared) b) (eq? (cadr shared) v))",
                )
                .unwrap();
            assert_eq!(read.last().unwrap().to_string(), expected);
        }
    }

    #[test]
    fn deep_clone_hash_key_cells_reaching_their_table_stay_isolated() {
        for first in ["j", "k"] {
            let second = if first == "j" { "k" } else { "j" };
            let mut template = Engine::new();
            register_gc(&mut template);
            template
                .run(format!(
                    "(define {first} (box #f))
                     (define {second} (box #f))
                     (define m (hash k 1))
                     (define f (let ((captured m)) (lambda () captured)))
                     (set-box! k f)
                     (set-box! j m)"
                ))
                .unwrap();
            let mut copy = template.deep_clone();
            drop(template);
            let result = copy
                .run(
                    "(probe-gc) (probe-gc)
                     (list (eq? (unbox k) f) (eq? ((unbox k)) (unbox j))
                           (eq? (car (hash-keys->list ((unbox k)))) k)
                           (hash-ref (unbox j) k))",
                )
                .unwrap();
            assert_eq!(
                result.last().unwrap().to_string(),
                "(#true #true #true 1)",
                "allocation order {first} first"
            );
        }
    }

    #[test]
    fn deep_clone_hash_keys_survive_template_collection() {
        let mut template = Engine::new();
        register_gc(&mut template);
        template
            .run(
                "(define key (box (value->iterator (list 1 2))))
             (define nested-key (list key))
             (define table (hash key 42 nested-key 43))
             (define members (hashset key nested-key))",
            )
            .unwrap();
        let mut copy = template.deep_clone();
        drop(template);
        let result = copy
            .run(
                "(probe-gc) (probe-gc)
             (list (hash-ref table key) (hash-ref table nested-key)
                   (hash-contains? table key) (hashset-contains? members key)
                   (hashset-contains? members nested-key))",
            )
            .unwrap();
        assert_eq!(
            result.last().unwrap().to_string(),
            "(42 43 #true #true #true)"
        );
    }

    #[test]
    fn deep_clones_remap_streams_transducers_reducers_and_iterators() {
        for drop_template_first in [true, false] {
            let mut template = Engine::new();
            // Each closure captures its box, so only the remapper can rewrite it.
            template
                .run(
                    "(define sb (box 1))
                     (define s (let ((b sb)) (stream-cons 0 (lambda () (unbox b)))))
                     (define tb (box 1))
                     (define t (let ((b tb)) (mapping (lambda (x) (+ x (unbox b))))))
                     (define rb (box 1))
                     (define r (let ((b rb)) (into-reducer (lambda (acc x) (+ acc x (unbox b))) 0)))
                     (define fb (box 0))
                     (define fe (let ((b fb)) (into-for-each (lambda (x) (set-box! b x)))))
                     (define ib (box 1))
                     (define it (value->iterator (list ib)))",
                )
                .unwrap();
            let template_heap = std::sync::Arc::downgrade(&template.virtual_machine.heap);
            let mut copy = template.deep_clone();
            copy.run(
                "(set-box! sb 2) (set-box! tb 2) (set-box! rb 2) (set-box! ib 2)
                 (transduce (list 7) (mapping (lambda (x) x)) fe)",
            )
            .unwrap();
            let (mut survivor, expected) = if drop_template_first {
                drop(template);
                // Nothing in the copy needs the template's cells.
                assert!(template_heap.upgrade().is_none());
                (copy, "(2 (2) 2 7 #true 2)")
            } else {
                drop(copy);
                (template, "(1 (1) 1 0 #true 1)")
            };
            let read = survivor
                .run(
                    "(list ((#%stream-cdr s))
                           (transduce (list 0) t (into-list))
                           (transduce (list 0) (mapping (lambda (x) x)) r)
                           (unbox fb)
                           (eq? (iter-next! it) ib)
                           (unbox ib))",
                )
                .unwrap();
            assert_eq!(read.last().unwrap().to_string(), expected);
        }
    }

    #[test]
    fn deep_clones_remap_continuations() {
        use crate::{gc::shared::ShareableMut, steel_vm::vm::ContinuationMark, SteelVal};

        let mut template = Engine::new();
        template
            .run(
                "(define kb (box 1))
                 (define saved #f)
                 (define (capture)
                   (let ((b kb))
                     (#%prim.call/cc (lambda (k) (set! saved k)))
                     (unbox b)))
                 (capture)",
            )
            .unwrap();
        let template_heap = std::sync::Arc::downgrade(&template.virtual_machine.heap);
        let copy = template.deep_clone();
        drop(template);
        assert!(template_heap.upgrade().is_none());

        let SteelVal::HeapAllocated(kb) = copy.extract_value("kb").unwrap() else {
            panic!("expected a box");
        };
        let SteelVal::ContinuationFunction(saved) = copy.extract_value("saved").unwrap() else {
            panic!("expected a continuation");
        };
        let mark = saved.inner.read();
        let ContinuationMark::Closed(closed) = &*mark else {
            panic!("expected a closed continuation");
        };
        // The captured local refers to the copy's box, which outlives the template.
        assert!(closed.stack.iter().any(|value| matches!(
            value,
            SteelVal::HeapAllocated(cell) if cell.ptr_eq(&kb)
        )));
    }

    #[test]
    fn deep_clones_retain_shared_custom_values_that_reach_template_cells() {
        use crate::{
            rvals::{AsRefSteelVal, Custom},
            steel_vm::register_fn::RegisterFn,
            values::closed::MarkAndSweepContext,
            SteelVal,
        };

        struct Holder(SteelVal);
        impl Custom for Holder {
            fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
                use crate::rvals::cycles::BreadthFirstSearchSteelValVisitor;
                context.push_back(self.0.clone());
            }
        }

        let mut template = Engine::new();
        template.register_fn("make-holder", Holder);
        register_gc(&mut template);
        template.register_fn("holder-value", |holder: SteelVal| {
            Holder::as_ref(&holder).map(|holder| holder.0.clone())
        });
        template
            .run("(define h (let ((b (box 1))) (make-holder (lambda () (unbox b)))))")
            .unwrap();
        let template_heap = std::sync::Arc::downgrade(&template.virtual_machine.heap);
        let mut copy = template.deep_clone();
        drop(template);
        // The shared holder still refers to the template's box, so the copy keeps it.
        assert_eq!(
            copy.run("((holder-value h))").unwrap().last(),
            Some(&SteelVal::IntV(1))
        );
        copy.run("(define borrowed (holder-value h)) (set! h #f)")
            .unwrap();
        copy.run("(probe-gc)").unwrap();
        assert_eq!(
            copy.run("(borrowed)").unwrap().last(),
            Some(&SteelVal::IntV(1))
        );
        copy.run("(set! borrowed #f)").unwrap();
        copy.run("(probe-gc) (probe-gc)").unwrap();
        assert!(template_heap.upgrade().is_none());
    }

    #[test]
    fn deep_clones_release_shared_values_individually() {
        use crate::{
            rvals::{cycles::BreadthFirstSearchSteelValVisitor, Custom},
            steel_vm::register_fn::RegisterFn,
            values::closed::MarkAndSweepContext,
            SteelVal,
        };
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        if !in_teardown_child("deep_clones_release_shared_values_individually") {
            return;
        }

        struct Holder(SteelVal, Arc<AtomicUsize>);
        impl Custom for Holder {
            fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
                context.push_back(self.0.clone());
            }
        }
        impl Drop for Holder {
            fn drop(&mut self) {
                self.1.fetch_add(1, Ordering::Relaxed);
            }
        }

        let dropped = Arc::new(AtomicUsize::new(0));
        let factory = dropped.clone();
        let mut source = Engine::new();
        register_gc(&mut source);
        source.register_fn("make-holder", move |value: SteelVal| {
            Holder(value, factory.clone())
        });
        source
            .run("(define first-holder (make-holder (box 1))) (define second-holder (make-holder (box 2)))")
            .unwrap();
        let source_heap = Arc::downgrade(&source.virtual_machine.heap);
        let mut copy = source.deep_clone();
        drop(source);
        copy.run("(probe-gc)").unwrap();
        assert_eq!(dropped.load(Ordering::Relaxed), 0);
        copy.run("(set! first-holder #f)").unwrap();
        copy.run("(probe-gc)").unwrap();
        assert_eq!(dropped.load(Ordering::Relaxed), 1);
        assert!(source_heap.upgrade().is_some());
        copy.run("(set! second-holder #f)").unwrap();
        copy.run("(probe-gc)").unwrap();
        assert_eq!(dropped.load(Ordering::Relaxed), 2);
        assert!(source_heap.upgrade().is_none());
    }

    #[test]
    fn sibling_clones_release_shared_values() {
        use crate::{
            rvals::{cycles::BreadthFirstSearchSteelValVisitor, Custom},
            steel_vm::register_fn::RegisterFn,
            values::closed::MarkAndSweepContext,
            SteelVal,
        };
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        struct Holder(SteelVal, Arc<AtomicUsize>);
        impl Custom for Holder {
            fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
                context.push_back(self.0.clone());
            }
        }
        impl Drop for Holder {
            fn drop(&mut self) {
                self.1.fetch_add(1, Ordering::Relaxed);
            }
        }

        let dropped = Arc::new(AtomicUsize::new(0));
        let factory = dropped.clone();
        let mut source = Engine::new();
        register_gc(&mut source);
        source.register_fn("make-holder", move |value: SteelVal| {
            Holder(value, factory.clone())
        });
        source
            .run("(define first-holder (make-holder (box 1)))")
            .unwrap();
        let source_heap = Arc::downgrade(&source.virtual_machine.heap);
        let mut first = source.deep_clone();
        let mut second = source.deep_clone();
        drop(source);
        // Each clone's retention must not keep the other's reachable.
        first.run("(set! first-holder #f)").unwrap();
        second.run("(set! first-holder #f)").unwrap();
        first.run("(probe-gc)").unwrap();
        second.run("(probe-gc)").unwrap();
        first.run("(probe-gc)").unwrap();
        assert_eq!(dropped.load(Ordering::Relaxed), 1);
        assert!(source_heap.upgrade().is_none());
    }

    #[test]
    fn clones_of_clones_keep_the_original_template_cells() {
        use crate::{
            rvals::{cycles::BreadthFirstSearchSteelValVisitor, AsRefSteelVal, Custom},
            steel_vm::register_fn::RegisterFn,
            values::closed::MarkAndSweepContext,
            SteelVal,
        };

        struct Holder(SteelVal);
        impl Custom for Holder {
            fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
                context.push_back(self.0.clone());
            }
        }

        let mut template = Engine::new();
        register_gc(&mut template);
        template.register_fn("make-holder", Holder);
        template.register_fn("holder-value", |holder: SteelVal| {
            Holder::as_ref(&holder).map(|holder| holder.0.clone())
        });
        template.run("(define h (make-holder (box 1)))").unwrap();
        let mut middle = template.deep_clone();
        drop(template);
        // The last clone shares the holder, which reaches only the first template's box.
        let mut last = middle.deep_clone();
        middle.run("(set! h #f)").unwrap();
        middle.run("(probe-gc) (probe-gc)").unwrap();
        last.run("(probe-gc)").unwrap();
        assert_eq!(
            last.run("(unbox (holder-value h))").unwrap().last(),
            Some(&SteelVal::IntV(1))
        );
    }

    #[test]
    fn deep_clone_keeps_list_tails_distinct() {
        // Appending shares the prefix's storage and offset, so only the tails differ.
        let mut template = Engine::new();
        template
            .run(
                "(define prefix (map box (range 0 50)))
                 (define left (append prefix (list 'left)))
                 (define right (append prefix (list 'right)))",
            )
            .unwrap();
        let mut copy = template.deep_clone();
        let read = copy
            .run(
                "(list (length prefix) (length left) (length right)
                       (list-ref left 50) (list-ref right 50))",
            )
            .unwrap();
        assert_eq!(read.last().unwrap().to_string(), "(50 51 51 left right)");
    }

    #[test]
    fn deep_clone_keeps_list_suffixes_shared() {
        // The cdr must stay a view of the copied list whichever of the two is reached first.
        for program in [
            "(define xs (list (box 1) (box 2) (box 3)))
             (define ys (cdr xs))",
            "(define ys #f)
             (define xs (list (box 1) (box 2) (box 3)))
             (set! ys (cdr xs))",
        ] {
            let mut template = Engine::new();
            template.run(program).unwrap();
            let mut copy = template.deep_clone();
            drop(template);
            let read = copy
                .run(
                    "(set-box! (car ys) 20)
                     (list (eq? (cdr xs) ys) (eq? (car ys) (cadr xs)) (unbox (cadr xs)))",
                )
                .unwrap();
            assert_eq!(read.last().unwrap().to_string(), "(#true #true 20)");
        }
    }

    #[test]
    fn deep_clone_reconnects_contracts_that_refer_to_their_closure() {
        // Dropping the template releases its heap, so a contract still holding the template's
        // closure would read a dead cell. Collection is not run: marking does not yet stop at
        // a closure that its own contract reaches.
        let mut template = Engine::new();
        template
            .run(
                "(struct holder (f))
                 (define f
                   (let ((b (box 0)))
                     (lambda () (set-box! b (+ (unbox b) 1)) (unbox b))))
                 (attach-contract-struct! f (holder f))",
            )
            .unwrap();
        let mut copy = template.deep_clone();
        drop(template);
        let read = copy
            .run(
                "(f)
                 (define contracted (holder-f (get-contract-struct f)))
                 (list (eq? contracted f) (contracted))",
            )
            .unwrap();
        assert_eq!(read.last().unwrap().to_string(), "(#true 2)");
    }

    #[test]
    fn deep_clone_rebuilds_tails_their_own_elements_refer_to() {
        // Each element closes over the list it is consed onto. Consing onto a mostly full
        // node links to that node, so an element's tail is its own list's cdr.
        let mut template = Engine::new();
        template
            .run(
                "(define (push x st) (cons (let ((b (box x))) (lambda (k) (if k b st))) st))
                 (define s (push 4 (push 3 (push 2 (push 1 (push 0 '()))))))",
            )
            .unwrap();
        assert_eq!(
            template.run("(eq? ((cadr s) #f) (cddr s))").unwrap().last(),
            Some(&crate::SteelVal::BoolV(true))
        );
        let mut copy = template.deep_clone();
        copy.run("(set-box! ((car ((cadr s) #f)) #t) 99)").unwrap();
        assert_eq!(
            template.run("(unbox ((caddr s) #t))").unwrap().last(),
            Some(&crate::SteelVal::IntV(2))
        );
        drop(template);
        let read = copy
            .run("(list (unbox ((car ((cadr s) #f)) #t)) (unbox ((caddr s) #t)))")
            .unwrap();
        assert_eq!(read.last().unwrap().to_string(), "(99 99)");

        // A list whose first element is its own tail.
        let mut template = Engine::new();
        template
            .run("(define s (list (box 1) 2 3)) (define l (cons s s))")
            .unwrap();
        assert_eq!(
            template.run("(eq? (cdr l) s)").unwrap().last(),
            Some(&crate::SteelVal::BoolV(true))
        );
        let mut copy = template.deep_clone();
        copy.run("(set-box! (car s) 99)").unwrap();
        assert_eq!(
            template.run("(unbox (car s))").unwrap().last(),
            Some(&crate::SteelVal::IntV(1))
        );
        drop(template);
        let read = copy
            .run("(list (unbox (car s)) (unbox (cadr l)) (unbox (car (car l))))")
            .unwrap();
        assert_eq!(read.last().unwrap().to_string(), "(99 99 99)");
    }

    #[test]
    fn recycling_keeps_the_slots_that_kept_slots_refer_to() {
        // The closures are built at run time, so no call is inlined into its caller.
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine
            .run(
                "(require-builtin steel/base)
                 (define c (let ((tag 'c)) (lambda () (list tag))))
                 (define b (let ((tag 'b)) (lambda () (list tag (c)))))
                 (define a (let ((tag 'a)) (lambda () (list tag (b)))))
                 (define keep a)",
            )
            .unwrap();
        // Only `keep` still reaches the old `a`, whose old `b` calls the old `c`.
        engine
            .run("(define c 0) (define b 0) (define a 0)")
            .unwrap();
        // Redefining past the threshold recycles the shadowed slots.
        for i in 0.. {
            engine.run(format!("(define x {i})")).unwrap();
            let compiler = engine.virtual_machine.compiler.read();
            if compiler.symbol_map.free_list.shadowed_count() == 0 {
                break;
            }
            assert!(i < 200, "shadowed slots were never recycled");
        }
        assert_eq!(
            engine.run("(keep)").unwrap().last().unwrap().to_string(),
            "(a (b (c)))"
        );
    }

    #[test]
    fn deep_clones_retain_other_heaps_cells_that_reach_template_cells() {
        // The vector belongs to another engine's heap, so neither copy owns it.
        let mut other = Engine::new();
        other.run("(define F (vector #f))").unwrap();
        let mut template = Engine::new();
        template.register_value("F", other.extract_value("F").unwrap());
        template
            .run("(vector-set! F 0 (let ((n 0)) (lambda () (set! n (+ n 1)) n)))")
            .unwrap();
        let mut copy = template.deep_clone();
        drop(template);
        assert_eq!(
            copy.run("((vector-ref F 0))").unwrap().last(),
            Some(&crate::SteelVal::IntV(1))
        );
        drop(other);
    }

    #[test]
    fn deep_clones_keep_struct_property_cells_the_template_drops() {
        let mut template = Engine::new();
        register_gc(&mut template);
        template
            .run("(define p (let () (struct holder (x) #:payload (box 42)) (holder 1)))")
            .unwrap();
        let template_heap = std::sync::Arc::downgrade(&template.virtual_machine.heap);
        let mut copy = template.deep_clone();
        let payload = "(unbox (#%struct-property-ref p '#:payload))";
        // Only the copy's instance still reaches the type, whose properties live in the vtable.
        // A `set!` returns the old value, which stays rooted until its program finishes.
        template.run("(set! p #f)").unwrap();
        template.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(
            copy.run(payload).unwrap().last(),
            Some(&crate::SteelVal::IntV(42))
        );
        drop(template);
        assert_eq!(
            copy.run(payload).unwrap().last(),
            Some(&crate::SteelVal::IntV(42))
        );
        // Once the copy no longer reaches the type, it releases the template's storage.
        copy.run("(set! p #f)").unwrap();
        copy.run("(probe-gc) (probe-gc)").unwrap();
        assert!(template_heap.upgrade().is_none());
    }

    #[test]
    fn closed_heaps_reclaim_cycles_as_pending_roots_are_released() {
        use std::sync::{atomic::Ordering, Arc};

        let mut engine = Engine::new_raw_no_kernel();
        let heap = Arc::downgrade(&engine.virtual_machine.heap);
        let dropped = store_thread_clone(&mut engine, false);
        let first_result = (
            engine.extract_value("stored-thread").unwrap().as_rooted(),
            engine.virtual_machine.heap.clone_for_storage(),
        );
        let other = crate::SteelVal::HeapAllocated(
            engine
                .virtual_machine
                .heap
                .lock()
                .allocate_without_collection(crate::SteelVal::IntV(42)),
        );
        let second_result = (
            other.as_rooted(),
            engine.virtual_machine.heap.clone_for_storage(),
        );
        drop(engine);
        assert_eq!(dropped.load(Ordering::SeqCst), 0);
        drop(first_result);
        assert_eq!(dropped.load(Ordering::SeqCst), 1);
        assert_eq!(
            second_result.0.value().as_box_to_inner(),
            Some(crate::SteelVal::IntV(42))
        );
        drop(second_result);
        assert!(heap.upgrade().is_none());
    }

    #[cfg(feature = "sync")]
    #[test]
    fn teardown_can_run_during_another_engines_gc() {
        use std::sync::{atomic::Ordering, Arc, Barrier};

        let mut collector = Engine::new();
        register_gc(&mut collector);
        let value = collector
            .run("(define live (box (vector (box 42)))) live")
            .unwrap()
            .pop()
            .unwrap();
        let rooted = value.as_rooted();
        let barrier = Arc::new(Barrier::new(2));
        let worker_barrier = barrier.clone();
        let worker = std::thread::spawn(move || {
            let mut engine = Engine::new_raw_no_kernel();
            worker_barrier.wait();
            for pass in 0..100 {
                let heap = Arc::downgrade(&engine.virtual_machine.heap);
                let dropped = store_thread_clone(&mut engine, pass % 2 == 0);
                drop(engine);
                assert_eq!(dropped.load(Ordering::SeqCst), 1);
                assert!(heap.upgrade().is_none());
                engine = Engine::new_raw_no_kernel();
            }
        });
        barrier.wait();
        for _ in 0..100 {
            assert_eq!(
                collector
                    .run("(probe-gc) (unbox (vector-ref (unbox live) 0))")
                    .unwrap()
                    .pop(),
                Some(crate::SteelVal::IntV(42))
            );
        }
        worker.join().unwrap();
        drop(rooted);
    }

    // Joins from the host. The result stays valid only while the worker's heap is alive.
    #[cfg(feature = "sync")]
    fn join_thread(worker: &crate::SteelVal) -> crate::rvals::Result<crate::SteelVal> {
        use crate::{
            rvals::AsRefSteelVal,
            steel_vm::vm::threads::{thread_join_impl, ThreadHandle},
        };

        ThreadHandle::as_ref(worker)
            .and_then(|handle| thread_join_impl(&handle))
            .map(|(result, _heap)| result.value().clone())
    }

    fn register_gc(engine: &mut Engine) {
        let mut primitives = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut primitives, true);
        let meta = primitives.builtin_modules().get("steel/meta").unwrap();
        engine.register_value(
            "probe-gc",
            meta.inner_map().get("#%gc-collect").unwrap().clone(),
        );
    }

    #[test]
    fn struct_properties_keep_heap_values_alive_before_first_instance() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run(
                "(define make-holder
                   (let ()
                     (struct holder () #:boxed (box 42) #:vector (vector (box 99)))
                     holder))",
            )
            .unwrap();
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(
            engine
                .run(
                    "(define owner (make-holder))
                     (unbox (#%struct-property-ref owner '#:boxed))
                     (unbox (vector-ref (#%struct-property-ref owner '#:vector) 0))",
                )
                .unwrap()[1..],
            [crate::SteelVal::IntV(42), crate::SteelVal::IntV(99)]
        );
    }

    #[test]
    fn struct_properties_preserve_closure_globals_during_recycling() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run(
                "(define target (box 42))
                 (define make-holder
                   (let ()
                     (struct holder () #:read (lambda () (unbox target)))
                     holder))",
            )
            .unwrap();
        engine.run("(define target (box 0))").unwrap();
        for _ in 0..150 {
            engine.run("(define shadowed 0)").unwrap();
        }
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(
            engine
                .run("((#%struct-property-ref (make-holder) '#:read))")
                .unwrap(),
            [crate::SteelVal::IntV(42)]
        );
    }

    #[test]
    fn struct_properties_allow_engine_teardown_and_later_collection() {
        use std::sync::Arc;

        let mut engine = Engine::new();
        let heap = Arc::downgrade(&engine.virtual_machine.heap);
        engine
            .run("(struct holder () #:boxed (box 42) #:vector (vector (box 99)))")
            .unwrap();
        drop(engine);
        assert!(heap.upgrade().is_none());

        let mut collector = Engine::new();
        register_gc(&mut collector);
        collector.run("(probe-gc) (probe-gc)").unwrap();
        for _ in 0..150 {
            collector.run("(define shadowed 0)").unwrap();
        }
        assert!(heap.upgrade().is_none());
    }

    #[test]
    fn cyclic_struct_properties_keep_heap_values_alive() {
        use crate::{
            gc::Gc,
            values::{
                structs::{StructTypeDescriptor, VTable},
                HashMap,
            },
            SteelVal,
        };

        // Restore the process-wide table even when an assertion fails.
        struct RestoreProperties(StructTypeDescriptor, Gc<HashMap<SteelVal, SteelVal>>);

        impl Drop for RestoreProperties {
            fn drop(&mut self) {
                VTable::set_entry(&self.0, None, self.1.clone());
            }
        }

        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run("(struct holder ()) (define owner (holder))")
            .unwrap();
        let SteelVal::CustomStruct(owner) = engine.extract_value("owner").unwrap() else {
            panic!("expected a struct");
        };
        let mut properties = HashMap::default();
        let payload = engine.run("(box 42)").unwrap().pop().unwrap();
        properties.insert(payload.clone(), SteelVal::CustomStruct(owner.clone()));
        let _restore = RestoreProperties(
            owner.type_descriptor,
            VTable::properties(owner.type_descriptor).unwrap(),
        );
        VTable::set_entry(&owner.type_descriptor, None, Gc::new(properties));
        engine.run("(probe-gc) (probe-gc)").unwrap();
        for _ in 0..150 {
            engine.run("(define shadowed 0)").unwrap();
        }
        assert_eq!(payload.as_box_to_inner(), Some(SteelVal::IntV(42)));
        let SteelVal::CustomStruct(property_owner) = owner.get(&payload).unwrap() else {
            panic!("expected the property to refer back to the struct");
        };
        assert!(Gc::ptr_eq(&property_owner, &owner));
    }

    #[test]
    fn unreachable_struct_types_release_property_heap_values() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        struct Probe(Arc<AtomicUsize>);
        impl crate::rvals::Custom for Probe {}
        impl Drop for Probe {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        // Each handle alone keeps the type's properties reachable.
        for handle in ["(holder)", "holder", "struct:holder"] {
            let drops = Arc::new(AtomicUsize::new(0));
            let factory = drops.clone();
            let mut engine = Engine::new();
            register_gc(&mut engine);
            engine.register_fn("make-probe", move || Probe(factory.clone()));
            engine
                .run(format!(
                    "(define owner
                       (let ()
                         (struct holder () #:payload (box (make-probe)))
                         {handle}))"
                ))
                .unwrap();
            engine.run("(probe-gc) (probe-gc)").unwrap();
            assert_eq!(
                drops.load(Ordering::SeqCst),
                0,
                "{handle} lost its properties"
            );
            engine.run("(set! owner #f)").unwrap();
            engine.run("(probe-gc) (probe-gc)").unwrap();
            assert_eq!(drops.load(Ordering::SeqCst), 1, "{handle} kept a dead type");
        }
    }

    #[test]
    fn registered_module_exports_keep_struct_properties() {
        use crate::{steel_vm::builtin::BuiltInModule, values::structs::VTable, SteelVal};

        let mut engine = Engine::new();
        register_gc(&mut engine);
        let constructor = engine
            .run("(let () (struct holder () #:payload (box 42)) holder)")
            .unwrap()
            .pop()
            .unwrap();
        let mut module = BuiltInModule::new("test/holder");
        module.register_value("make-holder", constructor);
        engine.register_module(module);
        // Only the module refers to the constructor until it is imported.
        engine.run("(probe-gc) (probe-gc)").unwrap();
        let SteelVal::CustomStruct(holder) = engine
            .run("(require-builtin test/holder) (make-holder)")
            .unwrap()
            .pop()
            .unwrap()
        else {
            panic!("expected a struct");
        };
        let properties = VTable::properties(holder.type_descriptor).unwrap();
        let Some(SteelVal::HeapAllocated(payload)) =
            properties.get(&SteelVal::SymbolV("#:payload".into()))
        else {
            panic!("expected a boxed payload");
        };
        assert_eq!(payload.get(), SteelVal::IntV(42));
    }

    #[cfg(not(feature = "without-drop-protection"))]
    #[test]
    fn pairs_sharing_a_child_drop_iteratively() {
        use crate::{values::lists::Pair, SteelVal};

        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                #[cfg(all(feature = "sync", feature = "biased"))]
                steel_rc::register_thread();
                // Both fields hold the next node, so each count is two until one field drops.
                let mut node = SteelVal::IntV(0);
                for _ in 0..100_000 {
                    node = Pair::cons(node.clone(), node).into();
                }
                drop(node);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn serialized_struct_types_keep_property_heap_values() {
        use crate::{values::structs::VTable, SteelVal};

        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run(
                "(define serialized
                   (let ()
                     (struct holder () #:payload (box 42))
                     (serialize-value holder)))",
            )
            .unwrap();
        engine.run("(probe-gc) (probe-gc)").unwrap();
        engine
            .run("(define restored ((deserialize-value serialized)))")
            .unwrap();
        let SteelVal::CustomStruct(restored) = engine.extract_value("restored").unwrap() else {
            panic!("expected a struct");
        };
        let properties = VTable::properties(restored.type_descriptor).unwrap();
        let Some(SteelVal::HeapAllocated(payload)) =
            properties.get(&SteelVal::SymbolV("#:payload".into()))
        else {
            panic!("expected a boxed payload");
        };
        assert_eq!(payload.get(), SteelVal::IntV(42));
    }

    #[test]
    fn eq_compares_identity_for_boxes_structs_and_rationals() {
        let mut engine = Engine::new();
        let results = engine
            .run(
                "(struct point (x))
                 (define p (point 1))
                 (define b (box 1))
                 (list (eq? b b) (eq? p p) (eqv? p p) (eq? p (point 1))
                       (eq? (box 1) (box 1)) (eqv? 1/2 1/2))",
            )
            .unwrap();
        assert_eq!(
            results.last().unwrap().to_string(),
            "(#true #true #true #false #false #true)"
        );
    }

    #[test]
    fn eqv_compares_numbers_by_value() {
        let mut engine = Engine::new();
        let results = engine
            .run(
                "(define big (expt 10 30))
                 (define ratio (/ big 7))
                 (define complex (make-rectangular big 2))
                 (list (eqv? (expt 10 30) big)
                       (eqv? (/ (expt 10 30) 7) ratio)
                       (eqv? (make-rectangular (expt 10 30) 2) complex)
                       (pair? (memv (/ (expt 10 30) 7) (list 1 ratio)))
                       (pair? (assv (/ (expt 10 30) 7) (list (cons ratio 'found))))
                       (eqv? 1/2 0.5)
                       (eqv? ratio (exact->inexact ratio))
                       (eqv? (make-rectangular 1 2) (make-rectangular 1.0 2))
                       (eqv? ratio (/ big 9)))",
            )
            .unwrap();
        assert_eq!(
            results.last().unwrap().to_string(),
            "(#true #true #true #true #true #false #false #false #false)"
        );
    }

    #[test]
    fn eqv_holds_whenever_eq_does() {
        let mut engine = Engine::new();
        let results = engine
            .run(
                "(let ([z (make-rectangular +nan.0 1.0)])
                   (list (eq? z z) (eqv? z z) (pair? (memv z (list z)))))",
            )
            .unwrap();
        assert_eq!(results.last().unwrap().to_string(), "(#true #true #true)");
    }

    // The test body runs in a child process, either because a failure aborts inside a
    // thread-local destructor or because other tests' collections must not trace its roots.
    // Returns whether this is the child.
    fn in_teardown_child(test: &str) -> bool {
        use std::time::{Duration, Instant};

        const CHILD: &str = "STEEL_TEARDOWN_CHILD";
        if std::env::var_os(CHILD).is_some() {
            return true;
        }
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                &format!("steel_vm::tests::embedding_regressions::{test}"),
                "--nocapture",
            ])
            .env(CHILD, "1")
            .spawn()
            .unwrap();
        // An abort prints the whole recursive drop stack, which can take minutes.
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            if let Some(status) = child.try_wait().unwrap() {
                assert!(status.success(), "{test} child failed: {status}");
                return false;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("{test} child did not finish");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    // Releasing this recursively would overflow the thread's stack.
    fn deeply_nested_list() -> crate::SteelVal {
        let mut nested = crate::SteelVal::IntV(1);
        for _ in 0..100_000 {
            nested = crate::SteelVal::ListV(vec![nested].into());
        }
        nested
    }

    #[cfg(feature = "sync")]
    #[test]
    fn retired_worker_releases_deeply_nested_list() {
        if !in_teardown_child("retired_worker_releases_deeply_nested_list") {
            return;
        }

        let value = std::thread::spawn(deeply_nested_list).join().unwrap();
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || drop(value))
            .unwrap()
            .join()
            .unwrap();
    }

    #[cfg(not(feature = "sync"))]
    #[test]
    fn vtable_teardown_releases_nested_lists_without_list_storage() {
        use crate::{gc::Gc, values::structs::VTable, SteelVal};

        if !in_teardown_child("vtable_teardown_releases_nested_lists_without_list_storage") {
            return;
        }

        std::thread::spawn(|| {
            // Create im-lists' empty-list storage after the table, so it is destroyed first.
            let descriptor = VTable::new_entry("teardown-order".into(), None, None);
            drop(crate::values::lists::List::<SteelVal>::new());
            let mut properties = crate::values::HashMap::default();
            properties.insert(SteelVal::SymbolV("#:fields".into()), deeply_nested_list());
            VTable::set_entry(&descriptor, None, Gc::new(properties));
        })
        .join()
        .unwrap();
    }

    #[cfg(not(feature = "sync"))]
    #[test]
    fn root_teardown_releases_nested_lists_without_list_storage() {
        use crate::{values::lists::List, SteelVal};

        if !in_teardown_child("root_teardown_releases_nested_lists_without_list_storage") {
            return;
        }

        std::thread::spawn(|| {
            // Register the root table before im-lists' empty-list storage, so it is destroyed
            // later. Leaking the tokens leaves the table the only owner of each value.
            core::mem::forget(SteelVal::IntV(0).mark_rooted());
            drop(List::<SteelVal>::new());
            core::mem::forget(deeply_nested_list().mark_rooted());
        })
        .join()
        .unwrap();
    }

    #[test]
    fn thread_local_engine_teardown_releases_lists_without_list_storage() {
        use std::cell::RefCell;

        if !in_teardown_child("thread_local_engine_teardown_releases_lists_without_list_storage") {
            return;
        }

        thread_local! {
            static ENGINE: RefCell<Option<Engine>> = const { RefCell::new(None) };
        }

        std::thread::spawn(|| {
            #[cfg(all(feature = "sync", feature = "biased"))]
            steel_rc::register_thread();
            // Register this slot before the engine creates im-lists' empty-list storage, so the
            // engine is dropped after that storage is destroyed.
            ENGINE.with(|_| {});
            let mut engine = Engine::new_raw_no_kernel();
            engine.register_value("nested", deeply_nested_list());
            ENGINE.with(|slot| *slot.borrow_mut() = Some(engine));
        })
        .join()
        .unwrap();
    }

    #[cfg(feature = "sync")]
    #[test]
    fn thread_local_engine_teardown_traces_lists_without_list_storage() {
        use crate::steel_vm::vm::threads::thread_finished;
        use std::{
            cell::RefCell,
            time::{Duration, Instant},
        };

        if !in_teardown_child("thread_local_engine_teardown_traces_lists_without_list_storage") {
            return;
        }

        thread_local! {
            static WORKER: RefCell<Option<crate::SteelVal>> = const { RefCell::new(None) };
            static ENGINE: RefCell<Option<Engine>> = const { RefCell::new(None) };
        }

        std::thread::spawn(|| {
            #[cfg(all(feature = "sync", feature = "biased"))]
            steel_rc::register_thread();
            // Register both slots before the engine creates im-lists' empty-list storage. The
            // pending result keeps the heap's storage, so dropping the engine after that
            // storage is destroyed traces the result's rooted list.
            WORKER.with(|_| {});
            ENGINE.with(|_| {});
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            let worker = engine
                .run(
                    "(require-builtin steel/base) (require-builtin steel/threads)
                     (spawn-native-thread (lambda () (list 1 2 3)))",
                )
                .unwrap()
                .pop()
                .unwrap();
            engine.enter_safepoint(|| {
                let deadline = Instant::now() + Duration::from_secs(10);
                while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                    assert!(Instant::now() < deadline, "worker did not finish");
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            WORKER.with(|slot| *slot.borrow_mut() = Some(worker));
            ENGINE.with(|slot| *slot.borrow_mut() = Some(engine));
        })
        .join()
        .unwrap();
    }

    #[test]
    fn execution_results_survive_later_collections() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        let results = engine
            .run("(box 42) (vector 42) (probe-gc) (probe-gc) (probe-gc)")
            .unwrap();
        assert_eq!(
            results[0].as_box_to_inner(),
            Some(crate::SteelVal::IntV(42))
        );
        let crate::SteelVal::MutableVector(vector) = &results[1] else {
            panic!("expected a mutable vector");
        };
        assert_eq!(vector.get(), [crate::SteelVal::IntV(42)]);
    }

    #[test]
    fn execution_result_roots_are_released_after_success_and_error() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::sync::Arc;

        if !in_teardown_child("execution_result_roots_are_released_after_success_and_error") {
            return;
        }

        #[derive(Clone)]
        struct Probe {
            _owner: Arc<()>,
        }
        impl crate::rvals::Custom for Probe {}

        let count = Arc::new(());
        let factory = count.clone();
        let mut engine = Engine::new();
        engine.register_fn("probe-value", move || Probe {
            _owner: factory.clone(),
        });
        register_gc(&mut engine);
        for last in ["void", "(error \"later expression\")"] {
            let result = engine.run(format!(
                "(box (probe-value)) (vector (probe-value)) (probe-gc) {last}"
            ));
            assert_eq!(result.is_err(), last != "void");
            drop(result);
            engine.run("(probe-gc) (probe-gc)").unwrap();
            assert_eq!(Arc::strong_count(&count), 2, "{last}");
        }
    }

    #[test]
    fn lowered_lets_round_trip_through_syntax_case() {
        let mut engine = Engine::new();
        engine
            .run(
                r#"
                (define-syntax (identity stx)
                  (syntax-case stx () [(_ expression) #'expression]))
                (define-syntax with-let
                  (syntax-rules () [(_) (identity (let ((x 1)) x))]))
                (define-syntax with-nested-lets
                  (syntax-rules ()
                    [(_) (identity (let ((x (let ((y 1)) y))) (let ((z x)) z)))]))
                (define-syntax with-return
                  (syntax-rules ()
                    [(_) (identity (let ((x 1)) (let () (return! x))))]))
                "#,
            )
            .unwrap();
        for expression in [
            "(with-let)",
            "(with-nested-lets)",
            "((lambda () (with-return) 99))",
        ] {
            assert_eq!(
                engine.run(expression).unwrap(),
                [crate::SteelVal::IntV(1)],
                "{expression}"
            );
        }
    }

    #[test]
    fn abandoned_channel_cycles_release_payloads() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::sync::Arc;

        struct Probe(#[allow(dead_code)] Arc<()>);
        impl crate::rvals::Custom for Probe {}

        let count = Arc::new(());
        let factory = count.clone();
        let mut engine = Engine::new();
        engine.register_fn("probe-value", move || Probe(factory.clone()));
        register_gc(&mut engine);
        engine
            .run(
                "(map (lambda (i)
                        (let ((channels (channels/new)))
                          (channel/send (channels-sender channels)
                            (box (list (probe-value) (channels-receiver channels))))))
                      (range 10))",
            )
            .unwrap();
        assert_eq!(Arc::strong_count(&count), 12);
        for _ in 0..3 {
            engine.run("(probe-gc)").unwrap();
        }
        assert_eq!(Arc::strong_count(&count), 2);
    }

    #[test]
    fn queued_channel_cycles_terminate_collection_and_preserve_messages() {
        for message in ["receiver", "channels"] {
            let mut engine = Engine::new();
            register_gc(&mut engine);
            engine
                .run(
                    "(define channels (channels/new))
                     (define receiver (channels-receiver channels))",
                )
                .unwrap();

            for _ in 0..2 {
                engine
                    .run(format!(
                        "(channel/send (channels-sender channels) {message})
                         (channel/send (channels-sender channels) (box 42))
                         (probe-gc) (probe-gc)"
                    ))
                    .unwrap();
                assert_eq!(
                    engine
                        .run(format!("(eq? (channel/recv receiver) {message})"))
                        .unwrap(),
                    [crate::SteelVal::BoolV(true)],
                );
                assert_eq!(
                    engine.run("(unbox (channel/recv receiver))").unwrap(),
                    [crate::SteelVal::IntV(42)],
                );
            }
        }
    }

    #[test]
    fn pending_channel_values_survive_collection() {
        for receiver in ["receiver", "(channels-receiver channels)"] {
            let mut engine = Engine::new();
            register_gc(&mut engine);
            engine
                .run(
                    "(define channels (channels/new))
                     (define sender (channels-sender channels))
                     (define empty-channels (channels/new))",
                )
                .unwrap();
            if receiver == "receiver" {
                engine
                    .run("(define receiver (channels-receiver channels)) (set! channels #f)")
                    .unwrap();
            }

            for receive in ["channel/recv", "channel/try-recv"] {
                engine
                    .run(
                        "(channel/send sender (box 42))
                         (channel/send sender (vector (box 43)))
                         (probe-gc) (probe-gc)",
                    )
                    .unwrap();
                assert_eq!(
                    engine
                        .run(format!(
                            "(receivers-select (channels-receiver empty-channels) {receiver})"
                        ))
                        .unwrap(),
                    [crate::SteelVal::IntV(1)]
                );
                assert_eq!(
                    engine
                        .run(format!("(unbox ({receive} {receiver}))"))
                        .unwrap(),
                    [crate::SteelVal::IntV(42)]
                );
                engine.run("(probe-gc)").unwrap();
                assert_eq!(
                    engine
                        .run(format!("(unbox (vector-ref ({receive} {receiver}) 0))"))
                        .unwrap(),
                    [crate::SteelVal::IntV(43)]
                );
                assert_eq!(
                    engine
                        .run(format!(
                            "(empty-channel-object? (channel/try-recv {receiver}))"
                        ))
                        .unwrap(),
                    [crate::SteelVal::BoolV(true)]
                );
            }
        }
    }

    #[test]
    fn channel_values_release_payloads_after_consumption_or_disconnect() {
        use crate::{
            rvals::IntoSteelVal,
            steel_vm::vm::threads::{channel_send, Channels},
        };
        use std::sync::Arc;

        struct Probe(#[allow(dead_code)] Arc<()>);
        impl crate::rvals::Custom for Probe {}

        let count = Arc::new(());
        let mut engine = Engine::new();
        let channels = Channels::new();
        let sender = channels.sender();
        for receive in ["channel/recv", "channel/try-recv"] {
            let function = engine
                .run(format!("(lambda (receiver) ({receive} receiver))"))
                .unwrap()
                .pop()
                .unwrap();
            channel_send(&sender, Probe(count.clone()).into_steelval().unwrap()).unwrap();
            let value = engine
                .call_function_with_args(function, vec![channels.receiver()])
                .unwrap();
            assert_eq!(Arc::strong_count(&count), 2);
            drop(value);
            assert_eq!(Arc::strong_count(&count), 1);
        }

        channel_send(&sender, Probe(count.clone()).into_steelval().unwrap()).unwrap();
        drop(channels);
        assert_eq!(Arc::strong_count(&count), 1);
        assert!(channel_send(&sender, Probe(count.clone()).into_steelval().unwrap()).is_err());
        assert_eq!(Arc::strong_count(&count), 1);
        assert!(channel_send(&sender, crate::SteelVal::IntV(42))
            .unwrap_err()
            .to_string()
            .contains("42"));

        let channels = Channels::new();
        let receiver = channels.receiver();
        channel_send(
            &channels.sender(),
            Probe(count.clone()).into_steelval().unwrap(),
        )
        .unwrap();
        let rooted_receiver = receiver.as_rooted();
        drop(receiver);
        drop(channels);
        assert_eq!(Arc::strong_count(&count), 2);
        drop(rooted_receiver);
        assert_eq!(Arc::strong_count(&count), 1);

        let channels = Channels::new();
        let receiver = channels.receiver();
        drop(channels);
        engine.register_value("receiver", receiver);
        assert!(engine.run("(channel/recv receiver)").is_err());
        assert_eq!(
            engine
                .run("(disconnected-channel-object? (channel/try-recv receiver))")
                .unwrap(),
            [crate::SteelVal::BoolV(true)]
        );
    }

    #[cfg(feature = "sync")]
    #[test]
    fn channel_values_survive_concurrent_receive_and_collection() {
        use crate::steel_vm::vm::threads::thread_finished;
        use std::time::{Duration, Instant};

        let mut engine = Engine::new();
        register_gc(&mut engine);
        let worker = engine
            .run(
                "(define channels (channels/new))
                 (define sender (channels-sender channels))
                 (define receiver (channels-receiver channels))
                 (spawn-native-thread
                   (lambda ()
                     (map (lambda (i)
                            (unbox (vector-ref (unbox (channel/recv receiver)) 0)))
                          (range 32))))",
            )
            .unwrap()
            .pop()
            .unwrap();
        engine
            .run(
                "(map (lambda (i)
                        (channel/send sender (box (vector (box i))))
                        (probe-gc))
                      (range 32))",
            )
            .unwrap();
        // Disconnect after sending so a missing message cannot leave recv blocked.
        engine.run("(set! sender #f) (set! channels #f)").unwrap();
        engine.enter_safepoint(|| {
            let deadline = Instant::now() + Duration::from_secs(10);
            while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                assert!(Instant::now() < deadline, "receiver did not finish");
                std::thread::sleep(Duration::from_millis(1));
            }
        });
        assert_eq!(
            join_thread(&worker).unwrap(),
            crate::SteelVal::ListV((0..32).map(crate::SteelVal::IntV).collect())
        );
    }

    #[cfg(feature = "sync")]
    #[test]
    fn pending_thread_results_survive_collection_and_release_roots_after_join() {
        use crate::steel_vm::{register_fn::RegisterFn, vm::threads::thread_finished};
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        struct Probe(#[allow(dead_code)] Arc<()>);
        impl crate::rvals::Custom for Probe {}

        let count = Arc::new(());
        let factory = count.clone();
        let mut engine = Engine::new();
        engine.register_fn("probe-value", move || Probe(factory.clone()));
        register_gc(&mut engine);
        for (payload, reader) in [
            ("(box payload)", "(car (unbox joined))"),
            ("(vector 42 payload)", "(vector-ref joined 0)"),
        ] {
            // shortcut: keep probe owners alive until biased RC can reclaim exited workers' values.
            let worker = engine
                .run(format!(
                    "(define worker
                       (let ((payload (cons 42 (probe-value))))
                         (spawn-native-thread (lambda () {payload})))) worker"
                ))
                .unwrap()
                .pop()
                .unwrap();
            engine.enter_safepoint(|| {
                let deadline = Instant::now() + Duration::from_secs(10);
                while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                    assert!(Instant::now() < deadline, "worker did not finish");
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            engine.run("(probe-gc) (probe-gc)").unwrap();
            assert_eq!(Arc::strong_count(&count), 3);
            engine.run("(define joined (thread-join! worker))").unwrap();
            assert_eq!(engine.run(reader).unwrap(), [crate::SteelVal::IntV(42)]);
            assert!(engine.run("(thread-join! worker)").is_err());
            // set! returns the old value, which stays rooted until the execution ends.
            engine.run("(set! joined #f)").unwrap();
            engine.run("(probe-gc)").unwrap();
            // Collectors in concurrently running tests trace every registered root, including
            // the pending result, and hold copies of its payload until their own pass ends.
            let deadline = Instant::now() + Duration::from_secs(10);
            while Arc::strong_count(&count) != 2 {
                assert!(Instant::now() < deadline, "the joined payload stayed alive");
                std::thread::yield_now();
                engine.run("(probe-gc)").unwrap();
            }
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn discarded_shared_thread_results_release_source_heaps() {
        use crate::{
            rvals::Custom,
            steel_vm::{register_fn::RegisterFn, vm::threads::thread_finished},
        };
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        struct Probe(#[allow(dead_code)] Arc<()>);
        impl Custom for Probe {}

        let mut destination = Engine::new();
        register_gc(&mut destination);
        for alias in [None, Some("receiver"), Some("cell")] {
            let count = Arc::new(());
            let factory = count.clone();
            let mut source = Engine::new();
            source.register_fn("probe-value", move || Probe(factory.clone()));
            let heap = Arc::downgrade(&source.virtual_machine.heap);
            let worker = source
                .run(
                    "(spawn-native-thread
                   (lambda ()
                     (let ((channel (channels/new)))
                       (channel/send (channels-sender channel) (box (probe-value)))
                       channel)))",
                )
                .unwrap()
                .pop()
                .unwrap();
            source.enter_safepoint(|| {
                let deadline = Instant::now() + Duration::from_secs(10);
                while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                    assert!(Instant::now() < deadline, "worker did not finish");
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            drop(source);
            destination.register_value("worker", worker);
            destination
                .run("(define joined (thread-join! worker))")
                .unwrap();
            destination.run("(probe-gc)").unwrap();
            assert!(heap.upgrade().is_some());
            assert!(Arc::strong_count(&count) > 1);
            if let Some(alias) = alias {
                destination
                    .run("(define receiver (channels-receiver joined))")
                    .unwrap();
                if alias == "cell" {
                    destination
                        .run("(define cell (channel/recv receiver)) (set! receiver #f)")
                        .unwrap();
                }
                destination.run("(set! joined #f)").unwrap();
                destination.run("(probe-gc)").unwrap();
                assert!(
                    heap.upgrade().is_some(),
                    "alias {alias:?}: a live alias lost its source heap (payload count {})",
                    Arc::strong_count(&count)
                );
                if alias == "receiver" {
                    destination
                        .run("(define cell (channel/recv receiver)) (set! receiver #f)")
                        .unwrap();
                    destination.run("(probe-gc)").unwrap();
                }
                let value = destination.run("(unbox cell)").unwrap().pop().unwrap();
                assert!(matches!(value, crate::SteelVal::Custom(_)));
                drop(value);
                destination.run("(set! cell #f)").unwrap();
            }
            destination
                .run("(set! joined #f) (set! worker #f)")
                .unwrap();
            destination.run("(probe-gc) (probe-gc)").unwrap();
            // Collectors in concurrently running tests trace every registered root, including
            // the pending result, and hold copies of its payload until their own pass ends.
            let deadline = Instant::now() + Duration::from_secs(10);
            while Arc::strong_count(&count) != 1 || heap.strong_count() != 0 {
                assert!(
                    Instant::now() < deadline,
                    "alias {alias:?}: discarded result stayed rooted (payload count {}, heap count {})",
                    Arc::strong_count(&count), heap.strong_count()
                );
                std::thread::yield_now();
                destination.run("(probe-gc)").unwrap();
            }
            assert!(
                heap.upgrade().is_none(),
                "alias {alias:?}: discarded result retained its heap"
            );
            assert_eq!(Arc::strong_count(&count), 1, "alias {alias:?}");
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn joined_results_from_other_heaps_keep_shared_strong_boxes() {
        use crate::steel_vm::vm::threads::thread_finished;
        use std::time::{Duration, Instant};

        // A strong box lives outside any heap, so both engines can hold the same one.
        let shared = crate::SteelVal::boxed(crate::SteelVal::IntV(1));
        let mut destination = Engine::new();
        destination.register_value("shared", shared.clone());
        let mut source = Engine::new();
        source.register_value("shared", shared);
        let worker = source
            .run("(spawn-native-thread (lambda () (list shared (box 2))))")
            .unwrap()
            .pop()
            .unwrap();
        source.enter_safepoint(|| {
            let deadline = Instant::now() + Duration::from_secs(10);
            while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                assert!(Instant::now() < deadline, "worker did not finish");
                std::thread::sleep(Duration::from_millis(1));
            }
        });
        drop(source);
        destination.register_value("worker", worker);
        let read = destination
            .run(
                "(define joined (thread-join! worker))
                 (set-strong-box! (car joined) 3)
                 (list (eq? (car joined) shared) (unbox-strong shared) (unbox (cadr joined)))",
            )
            .unwrap();
        assert_eq!(read.last().unwrap().to_string(), "(#true 3 2)");
    }

    #[cfg(feature = "sync")]
    #[test]
    fn completed_thread_results_keep_originating_heap_alive() {
        use crate::steel_vm::vm::threads::thread_finished;
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        let mut collector = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut collector, true);
        register_gc(&mut collector);
        collector
            .run("(require-builtin steel/meta) (require-builtin steel/threads)")
            .unwrap();
        // The nested box checks that copied cells refer to each other's copies.
        for (payload, reader) in [
            ("(box 42)", "(unbox joined)"),
            ("(box (box 42))", "(unbox (unbox joined))"),
        ] {
            for join in [false, true] {
                let mut engine = Engine::new_raw_no_kernel();
                crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
                let heap = Arc::downgrade(&engine.virtual_machine.heap);
                let worker = engine
                    .run(format!(
                        "(require-builtin steel/meta)
                         (require-builtin steel/threads)
                         (spawn-native-thread (lambda () {payload}))"
                    ))
                    .unwrap()
                    .pop()
                    .unwrap();
                engine.enter_safepoint(|| {
                    let deadline = Instant::now() + Duration::from_secs(10);
                    while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                        assert!(Instant::now() < deadline, "worker did not finish");
                        std::thread::sleep(Duration::from_millis(1));
                    }
                });
                drop(engine);
                assert_eq!(
                    heap.strong_count(),
                    1,
                    "the pending result must own its heap"
                );
                collector.run("(probe-gc) (probe-gc)").unwrap();

                if join {
                    // Joining from another heap copies the result, so its heap is released.
                    collector.register_value("worker", worker.clone());
                    collector
                        .run("(define joined (thread-join! worker))")
                        .unwrap();
                    assert!(heap.upgrade().is_none());
                    assert_eq!(
                        collector
                            .run(format!("(probe-gc) {reader}"))
                            .unwrap()
                            .last(),
                        Some(&crate::SteelVal::IntV(42))
                    );
                    assert!(collector.run("(thread-join! worker)").is_err());
                    collector.run("(set! joined #f)").unwrap();
                }
                drop(worker);
                assert!(heap.upgrade().is_none());
                collector.run("(probe-gc) (probe-gc)").unwrap();
            }
        }
    }

    #[test]
    fn rooted_closures_keep_only_their_own_engines_shadowed_globals() {
        use crate::parser::interner::InternedString;

        fn slot(engine: &Engine, name: &str) -> usize {
            *engine
                .virtual_machine
                .compiler
                .read()
                .symbol_map
                .map()
                .get(&InternedString::from_str(name))
                .unwrap()
        }

        let mut other = Engine::new_raw_no_kernel();
        other.run("(define x 'other) (define (get-x) x)").unwrap();
        let foreign = other.extract_value("get-x").unwrap().as_rooted();

        let mut engine = Engine::new_raw_no_kernel();
        engine
            .run("(define x 'old) (define y 'old) (define (get-y) y)")
            .unwrap();
        // The other engine's closure refers to the same slot number as this engine's `x`.
        let shadowed = slot(&engine, "x");
        assert_eq!(shadowed, slot(&other, "x"));
        // Only the root reaches this engine's closure once `get-y` is redefined.
        let get_y = engine.extract_value("get-y").unwrap().as_rooted();
        engine.run("(define y 'new) (define (get-y) 'new)").unwrap();
        // Redefining past the threshold recycles the shadowed slots.
        for i in 0.. {
            engine.run(format!("(define x {i})")).unwrap();
            let compiler = engine.virtual_machine.compiler.read();
            if compiler.symbol_map.free_list.shadowed_count() == 0 {
                assert!(compiler.symbol_map.free_list.free_list.contains(&shadowed));
                break;
            }
            assert!(i < 200, "shadowed slots were never recycled");
        }
        assert_eq!(
            engine
                .call_function_with_args(get_y.value().clone(), Vec::new())
                .unwrap()
                .to_string(),
            "old"
        );
        drop((foreign, get_y));
    }

    // A value in a cell of another heap whose last copy, once a traversal has read and cleared
    // the cell, records whether `engine`'s heap was locked when it was dropped. Returns the
    // value to register in `engine` and the (dropped, locked) flags.
    #[cfg(feature = "sync")]
    fn foreign_copy_probe(
        engine: &Engine,
    ) -> (
        crate::SteelVal,
        std::sync::Arc<std::sync::atomic::AtomicBool>,
        std::sync::Arc<std::sync::atomic::AtomicBool>,
    ) {
        use crate::{
            rvals::{Custom, IntoSteelVal},
            steel_vm::vm::HeapState,
            values::closed::{Heap, HeapRef, MarkAndSweepContext},
            SteelVal,
        };
        use std::sync::{
            atomic::{AtomicBool, Ordering},
            Arc, Weak,
        };

        struct Probe {
            heap: Weak<HeapState>,
            dropped: Arc<AtomicBool>,
            locked: Arc<AtomicBool>,
        }
        impl Custom for Probe {}
        impl Drop for Probe {
            fn drop(&mut self) {
                let locked = self
                    .heap
                    .upgrade()
                    .is_some_and(|heap| heap.try_lock().is_none());
                self.locked.store(locked, Ordering::SeqCst);
                self.dropped.store(true, Ordering::SeqCst);
            }
        }

        // Clears the cell once a traversal has read it, as its own engine could meanwhile, so
        // the traversal's copy is the payload's last reference.
        struct Clearer(HeapRef<SteelVal>, #[allow(dead_code)] Heap);
        impl Custom for Clearer {
            fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
                if let Some(cell) = self.0.inner.upgrade() {
                    context.mark_heap_reference(&cell);
                }
                self.0.set_and_return(SteelVal::Void);
            }
        }

        let dropped = Arc::new(AtomicBool::new(false));
        let locked = Arc::new(AtomicBool::new(false));
        let probe = Probe {
            heap: Arc::downgrade(&engine.virtual_machine.heap),
            dropped: dropped.clone(),
            locked: locked.clone(),
        };
        let mut foreign = Heap::new();
        let cell = foreign.allocate_without_collection(probe.into_steelval().unwrap());
        let clearer = Clearer(cell, foreign).into_steelval().unwrap();
        (clearer, dropped, locked)
    }

    #[cfg(feature = "sync")]
    #[test]
    fn collections_release_copies_of_foreign_values_after_unlocking() {
        use std::sync::atomic::Ordering;

        let mut engine = Engine::new();
        register_gc(&mut engine);
        let (clearer, dropped, locked) = foreign_copy_probe(&engine);
        engine.register_value("clearer", clearer);
        engine.run("(probe-gc)").unwrap();
        assert!(dropped.load(Ordering::SeqCst), "the copy was not released");
        assert!(
            !locked.load(Ordering::SeqCst),
            "the copy was released under the heap lock"
        );
    }

    #[cfg(feature = "sync")]
    #[test]
    fn recycling_releases_copies_of_foreign_values_after_unlocking() {
        use std::sync::atomic::Ordering;

        let mut engine = Engine::new_raw_no_kernel();
        let (clearer, dropped, locked) = foreign_copy_probe(&engine);
        engine.register_value("clearer", clearer);
        // Redefining past the threshold recycles the shadowed slots.
        for i in 0.. {
            engine.run(format!("(define x {i})")).unwrap();
            if dropped.load(Ordering::SeqCst) {
                break;
            }
            assert!(i < 200, "the copy was not released");
        }
        assert_eq!(
            engine
                .virtual_machine
                .compiler
                .read()
                .symbol_map
                .free_list
                .shadowed_count(),
            0,
            "recycling released the copy"
        );
        assert!(
            !locked.load(Ordering::SeqCst),
            "the copy was released under the heap lock"
        );
    }

    // `(build leaf n)` nests `n` levels of `(list acc acc)` around `leaf`, so a walk that
    // visits each path separately takes 2^n steps. `(leaf v n)` reads the leaf back. Live
    // collection still walks each path, so tests rooting these run in a child process.
    const SHARED_DEPTH: usize = 40;
    const SHARED_SUBLISTS: &str = "
        (define (build acc n) (if (= n 0) acc (build (list acc acc) (- n 1))))
        (define (leaf v n) (if (= n 0) v (leaf (car v) (- n 1))))";

    fn shared_sublist_engine() -> Engine {
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine
            .run(format!(
                "(require-builtin steel/base) (require-builtin steel/meta) (require-builtin steel/threads)
                 {SHARED_SUBLISTS}"
            ))
            .unwrap();
        engine
    }

    #[test]
    fn teardown_traces_shared_sublists_once() {
        if !in_teardown_child("teardown_traces_shared_sublists_once") {
            return;
        }

        let mut engine = shared_sublist_engine();
        let results = engine
            .run(format!(
                "(define slices (let ((l (list (box 1) (box 2)))) (list l (cdr l) l)))
                 (build (list (box 42)) {SHARED_DEPTH})"
            ))
            .unwrap();
        let rooted = results.last().unwrap().as_rooted();
        // Either slice can be traced first; each reaches its own cells.
        let slices = engine.extract_value("slices").unwrap().as_rooted();
        drop(results);
        // A remaining handle makes the engine's drop trace the registered roots.
        let heap = engine.virtual_machine.heap.clone_for_storage();
        drop(engine);

        let mut value = rooted.value().clone();
        for _ in 0..SHARED_DEPTH {
            let crate::SteelVal::ListV(list) = value else {
                panic!("expected a list");
            };
            value = list.car().unwrap();
        }
        let crate::SteelVal::ListV(leaf) = value else {
            panic!("expected the leaf list");
        };
        assert_eq!(
            leaf.car().unwrap().as_box_to_inner(),
            Some(crate::SteelVal::IntV(42))
        );
        let crate::SteelVal::ListV(slices_list) = slices.value().clone() else {
            panic!("expected a list");
        };
        let boxes: Vec<_> = slices_list
            .iter()
            .flat_map(|slice| match slice {
                crate::SteelVal::ListV(slice) => slice.iter().cloned().collect::<Vec<_>>(),
                _ => panic!("expected a slice"),
            })
            .map(|cell| cell.as_box_to_inner())
            .collect();
        let [a, b, c, d, e] = [1, 2, 2, 1, 2].map(|x| Some(crate::SteelVal::IntV(x)));
        assert_eq!(boxes, [a, b, c, d, e]);
        drop((rooted, slices, heap));
    }

    #[cfg(feature = "sync")]
    #[test]
    fn joining_a_result_with_shared_sublists_from_another_heap() {
        use crate::steel_vm::vm::threads::thread_finished;
        use std::time::{Duration, Instant};

        if !in_teardown_child("joining_a_result_with_shared_sublists_from_another_heap") {
            return;
        }

        let mut collector = shared_sublist_engine();
        let mut engine = shared_sublist_engine();
        let worker = engine
            .run(format!(
                "(spawn-native-thread (lambda () (build (list (box 42)) {SHARED_DEPTH})))"
            ))
            .unwrap()
            .pop()
            .unwrap();
        engine.enter_safepoint(|| {
            let deadline = Instant::now() + Duration::from_secs(10);
            while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                assert!(Instant::now() < deadline, "worker did not finish");
                std::thread::sleep(Duration::from_millis(1));
            }
        });
        drop(engine);
        collector.register_value("worker", worker);
        assert_eq!(
            collector
                .run(format!(
                    "(define joined (thread-join! worker))
                     (unbox (car (leaf joined {SHARED_DEPTH})))"
                ))
                .unwrap()
                .last(),
            Some(&crate::SteelVal::IntV(42))
        );
    }

    #[cfg(feature = "sync")]
    #[test]
    fn rooted_values_survive_teardown_while_a_thread_result_is_pending() {
        use crate::steel_vm::vm::threads::thread_finished;
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        let heap = Arc::downgrade(&engine.virtual_machine.heap);
        let results = engine
            .run(
                "(require-builtin steel/meta)
                 (require-builtin steel/threads)
                 (define worker (spawn-native-thread (lambda () 0)))
                 (box 42)",
            )
            .unwrap();
        // A collection keeps a value held outside the heap only through a root, and so does
        // teardown.
        let rooted = results.last().unwrap().as_rooted();
        drop(results);
        let worker = engine.extract_value("worker").unwrap();
        engine.enter_safepoint(|| {
            let deadline = Instant::now() + Duration::from_secs(10);
            while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                assert!(Instant::now() < deadline, "worker did not finish");
                std::thread::sleep(Duration::from_millis(1));
            }
        });
        drop(engine);
        assert!(
            heap.upgrade().is_some(),
            "the pending result keeps the heap"
        );
        assert_eq!(
            rooted.value().as_box_to_inner(),
            Some(crate::SteelVal::IntV(42))
        );
        drop(rooted);
        drop(worker);
        assert!(heap.upgrade().is_none());
    }

    #[cfg(feature = "sync")]
    #[test]
    fn engine_teardown_releases_heap_stored_thread_handles() {
        use crate::steel_vm::{register_fn::RegisterFn, vm::threads::thread_finished};
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        if !in_teardown_child("engine_teardown_releases_heap_stored_thread_handles") {
            return;
        }

        struct Probe(#[allow(dead_code)] Arc<()>);
        impl crate::rvals::Custom for Probe {}

        for (container, clone_heap) in [
            ("box", false),
            ("vector", false),
            ("box", true),
            ("vector", true),
        ] {
            let count = Arc::new(());
            let factory = count.clone();
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            if clone_heap {
                let isolated = engine.deep_clone();
                let original_heap = Arc::downgrade(&engine.virtual_machine.heap);
                drop(engine);
                assert!(original_heap.upgrade().is_none());
                engine = isolated;
            }
            engine.register_fn("probe-value", move || Probe(factory.clone()));
            let heap = Arc::downgrade(&engine.virtual_machine.heap);
            let worker = engine
                .run(
                    "(require-builtin steel/meta)
                     (require-builtin steel/threads)
                     (require-builtin steel/vectors)
                     (define worker
                       (let ((payload (probe-value)))
                         (spawn-native-thread (lambda () (box payload)))))
                     worker",
                )
                .unwrap()
                .pop()
                .unwrap();
            engine.enter_safepoint(|| {
                let deadline = Instant::now() + Duration::from_secs(10);
                while thread_finished(&worker).unwrap() != crate::SteelVal::BoolV(true) {
                    assert!(Instant::now() < deadline, "worker did not finish");
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            engine
                .run(format!(
                    "(define owner ({container} worker)) (define live (box 42))"
                ))
                .unwrap();
            drop(worker);
            let mut survivor = engine.clone();
            drop(engine);
            assert_eq!(
                survivor.run("(unbox live)").unwrap(),
                [crate::SteelVal::IntV(42)]
            );
            drop(survivor);
            assert!(
                heap.upgrade().is_none(),
                "{container} must not retain the heap"
            );
            assert_eq!(
                Arc::strong_count(&count),
                1,
                "{container} must release the payload"
            );
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn engine_teardown_waits_for_running_workers() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        let (started_tx, started_rx) = crossbeam_channel::bounded(1);
        let (release_tx, release_rx) = crossbeam_channel::bounded(1);
        let mut engine = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
        engine.register_fn("wait-for-release", move || {
            started_tx.send(()).unwrap();
            release_rx.recv_timeout(Duration::from_secs(10)).unwrap();
        });
        let heap = Arc::downgrade(&engine.virtual_machine.heap);
        engine
            .run(
                "(require-builtin steel/meta)
                 (require-builtin steel/threads)
                 (define owner
                   (box (spawn-native-thread
                          (lambda ()
                            (define payload (box 42))
                            (wait-for-release)
                            payload))))",
            )
            .unwrap();
        engine.enter_safepoint(|| started_rx.recv_timeout(Duration::from_secs(10)).unwrap());
        drop(engine);
        assert!(
            heap.strong_count() > 0,
            "the running worker still needs its heap"
        );
        release_tx.send(()).unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while heap.strong_count() > 0 {
            // Biased RC defers cross-thread drops to the allocating thread.
            #[cfg(feature = "biased")]
            steel_rc::QueueHandle::run_explicit_merge();
            assert!(
                Instant::now() < deadline,
                "the completed worker retained its heap"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn discarded_completed_thread_handles_release_result_payloads() {
        use crate::steel_vm::{register_fn::RegisterFn, vm::threads::thread_finished};
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        struct Probe(#[allow(dead_code)] Arc<()>);
        impl crate::rvals::Custom for Probe {}

        let count = Arc::new(());
        let factory = count.clone();
        let mut engine = Engine::new();
        engine.register_fn("probe-value", move || Probe(factory.clone()));
        register_gc(&mut engine);

        for payload in ["(box payload)", "(vector payload)"] {
            let workers: Vec<_> = (0..10)
                .map(|_| {
                    engine
                        .run(format!(
                            "(let ((payload (probe-value)))
                               (spawn-native-thread (lambda () {payload})))"
                        ))
                        .unwrap()
                        .pop()
                        .unwrap()
                })
                .collect();
            engine.enter_safepoint(|| {
                let deadline = Instant::now() + Duration::from_secs(10);
                while workers
                    .iter()
                    .any(|worker| thread_finished(worker).unwrap() != crate::SteelVal::BoolV(true))
                {
                    assert!(Instant::now() < deadline, "workers did not finish");
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            assert_eq!(Arc::strong_count(&count), 12);
            drop(workers);
            engine.run("(probe-gc)").unwrap();
            // Collectors in concurrently running tests trace every registered root, including
            // these pending results, and hold copies until their own pass ends.
            let deadline = Instant::now() + Duration::from_secs(10);
            while Arc::strong_count(&count) != 2 {
                assert!(
                    Instant::now() < deadline,
                    "results retained their payloads: {payload}"
                );
                std::thread::yield_now();
                engine.run("(probe-gc)").unwrap();
            }
            assert_eq!(Arc::strong_count(&count), 2, "{payload}");

            engine
                .run(
                    "(map (lambda (i) (box (vector i))) (range 2000))
                     (probe-gc)",
                )
                .unwrap();
            assert_eq!(Arc::strong_count(&count), 2, "{payload}");
        }
    }

    #[test]
    fn idle_heap_operations_do_not_lock_thread_registry() {
        use crate::SteelVal;

        if !in_teardown_child("idle_heap_operations_do_not_lock_thread_registry") {
            return;
        }

        let mut engine = Engine::new();
        #[cfg(feature = "sync")]
        let callback = engine
            .run("(#%closure->boxed-function (lambda () 1))")
            .unwrap();
        #[cfg(feature = "sync")]
        let mut surviving_callback = callback.clone();
        #[cfg(feature = "sync")]
        drop(callback);
        let registry = engine.virtual_machine.synchronizer.threads.clone();

        for _ in 0..2 {
            {
                let _guard = registry.lock().unwrap();
                let cell = engine.virtual_machine.with_heap(None, |_, heap| {
                    SteelVal::HeapAllocated(heap.allocate_without_collection(SteelVal::IntV(42)))
                });
                assert_eq!(cell.as_box_to_inner(), Some(SteelVal::IntV(42)));
            }

            #[cfg(feature = "sync")]
            surviving_callback.clear();
            engine.virtual_machine.with_heap(None, |_, _| {});
            assert_eq!(registry.lock().unwrap().len(), 1);
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn completed_thread_cleanup_allows_reentrant_collection() {
        use crate::{
            rvals::IntoSteelVal,
            steel_vm::vm::{threads::thread_finished, Synchronizer},
            SteelVal,
        };
        use std::{
            sync::{
                atomic::{AtomicUsize, Ordering},
                Arc,
            },
            time::{Duration, Instant},
        };

        if !in_teardown_child("completed_thread_cleanup_allows_reentrant_collection") {
            return;
        }

        struct Probe {
            engine: Engine,
            synchronizer: Synchronizer,
            calls: Arc<AtomicUsize>,
        }
        impl crate::rvals::Custom for Probe {}
        impl Drop for Probe {
            fn drop(&mut self) {
                assert!(self.engine.virtual_machine.heap.try_lock().is_some());
                assert!(self.synchronizer.threads.try_lock().is_ok());
                self.engine.run("(probe-gc)").unwrap();
                self.calls.fetch_add(1, Ordering::SeqCst);
            }
        }

        for update in [false, true] {
            let mut engine = Engine::new();
            register_gc(&mut engine);
            engine
                .run(
                    "(define incoming #f)
                     (define (spawn-probe payload)
                       (spawn-native-thread (lambda () payload)))
                     (define (collect-with-live live)
                       (probe-gc)
                       (unbox live))",
                )
                .unwrap();
            let calls = Arc::new(AtomicUsize::new(0));
            let probe = Probe {
                engine: engine.clone(),
                synchronizer: engine.virtual_machine.synchronizer.clone(),
                calls: calls.clone(),
            }
            .into_steelval()
            .unwrap();
            let worker = engine
                .call_function_by_name_with_args("spawn-probe", vec![probe])
                .unwrap();
            engine.enter_safepoint(|| {
                let deadline = Instant::now() + Duration::from_secs(10);
                while thread_finished(&worker).unwrap() != SteelVal::BoolV(true) {
                    assert!(Instant::now() < deadline, "worker did not finish");
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            drop(worker);
            assert_eq!(calls.load(Ordering::SeqCst), 0);

            // Allocate without triggering cleanup before the value reaches the active call.
            let live = SteelVal::HeapAllocated(
                engine
                    .virtual_machine
                    .heap
                    .lock()
                    .allocate_without_collection(SteelVal::IntV(42)),
            );
            if update {
                assert!(engine.update_value("incoming", live).is_some());
                assert_eq!(
                    engine.extract_value("incoming").unwrap().as_box_to_inner(),
                    Some(SteelVal::IntV(42))
                );
            } else {
                assert_eq!(
                    engine
                        .call_function_by_name_with_args("collect-with-live", vec![live])
                        .unwrap(),
                    SteelVal::IntV(42)
                );
            }
            assert_eq!(calls.load(Ordering::SeqCst), 1);
            engine.run("(probe-gc)").unwrap();
            drop(engine);
            assert_eq!(calls.load(Ordering::SeqCst), 1);
        }
    }

    #[test]
    fn garbage_collection_runs_payload_destructors_after_unlocking() {
        use crate::rvals::IntoSteelVal;
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        if !in_teardown_child("garbage_collection_runs_payload_destructors_after_unlocking") {
            return;
        }

        struct Probe {
            engine: Engine,
            callbacks: Arc<AtomicUsize>,
        }
        impl crate::rvals::Custom for Probe {}
        impl Drop for Probe {
            fn drop(&mut self) {
                assert!(
                    self.engine.virtual_machine.heap.try_lock().is_some(),
                    "payload dropped under the heap lock"
                );
                assert_eq!(
                    self.engine
                        .run("(probe-gc) (unbox (box 42))")
                        .unwrap()
                        .last(),
                    Some(&crate::SteelVal::IntV(42))
                );
                self.callbacks.fetch_add(1, Ordering::SeqCst);
            }
        }

        for (vector, keep_handle, collect) in [
            (false, false, "(probe-gc)"),
            (false, true, "(probe-gc)"),
            (true, false, "(probe-gc)"),
            (true, true, "(probe-gc)"),
            (
                false,
                false,
                "(for-each (lambda (_) (assert! (= (unbox (box 42)) 42))) (range 1000))",
            ),
            (
                true,
                false,
                "(for-each (lambda (_) (assert! (= (vector-ref (vector 42) 0) 42))) (range 1000))",
            ),
            (
                true,
                false,
                "(for-each (lambda (_) (assert! (= (vector-ref (make-vector 1 42) 0) 42))) (range 1000))",
            ),
        ] {
            let mut engine = Engine::new();
            register_gc(&mut engine);
            let callbacks = Arc::new(AtomicUsize::new(0));
            let payload = Probe {
                engine: engine.clone(),
                callbacks: callbacks.clone(),
            }
            .into_steelval()
            .unwrap();
            let value = if vector {
                crate::SteelVal::MutableVector(
                    engine
                        .virtual_machine
                        .heap
                        .lock()
                        .allocate_vec_without_collection(vec![payload]),
                )
            } else {
                crate::SteelVal::HeapAllocated(
                    engine
                        .virtual_machine
                        .heap
                        .lock()
                        .allocate_without_collection(payload),
                )
            };
            // An unrooted handle survives weak collection but not mark-and-sweep.
            let discarded = keep_handle.then_some(value);
            engine
                .run(format!(
                    "(let ((live (box 7)))
                       {collect}
                       (assert! (= (unbox live) 7)))"
                ))
                .unwrap();
            assert_eq!(callbacks.load(Ordering::SeqCst), 1, "{collect}");
            drop(discarded);
        }
    }

    fn check_incoming_binding_survives_collection(update: bool) {
        use crate::{rvals::IntoSteelVal, SteelVal};
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        struct CollectOnDrop {
            engine: Engine,
            calls: Arc<AtomicUsize>,
        }
        impl crate::rvals::Custom for CollectOnDrop {}
        impl Drop for CollectOnDrop {
            fn drop(&mut self) {
                assert!(self.engine.virtual_machine.heap.try_lock().is_some());
                self.engine.run("(probe-gc)").unwrap();
                self.calls.fetch_add(1, Ordering::SeqCst);
            }
        }

        for queued in [false, true] {
            if queued && !cfg!(all(feature = "sync", feature = "biased")) {
                continue;
            }
            let mut engine = Engine::new();
            register_gc(&mut engine);
            assert!(engine.update_value("incoming", SteelVal::IntV(0)).is_none());
            if update {
                engine.register_value("incoming", SteelVal::IntV(0));
            }
            let collector = engine.clone();
            let incoming = engine.run("(box 42)").unwrap().pop().unwrap();
            let unrelated = engine
                .virtual_machine
                .heap
                .lock()
                .allocate_without_collection(SteelVal::IntV(99));
            let calls = Arc::new(AtomicUsize::new(0));
            let probe = CollectOnDrop {
                engine: collector,
                calls: calls.clone(),
            }
            .into_steelval()
            .unwrap();
            if queued {
                #[cfg(all(feature = "sync", feature = "biased"))]
                std::thread::spawn(move || drop(probe)).join().unwrap();
            } else {
                engine.virtual_machine.heap.lock().released.push(probe);
            }
            assert_eq!(calls.load(Ordering::SeqCst), 0);
            if update {
                assert!(engine.update_value("incoming", incoming).is_some());
            } else {
                engine.register_value("incoming", incoming);
            }
            assert_eq!(calls.load(Ordering::SeqCst), 1);
            assert_eq!(
                engine.extract_value("incoming").unwrap().as_box_to_inner(),
                Some(SteelVal::IntV(42))
            );
            assert_eq!(unrelated.get(), SteelVal::Void);
        }
    }

    #[test]
    fn registration_preserves_incoming_binding_during_deferred_destruction() {
        if in_teardown_child("registration_preserves_incoming_binding_during_deferred_destruction")
        {
            check_incoming_binding_survives_collection(false);
        }
    }

    #[test]
    fn update_preserves_incoming_binding_during_deferred_destruction() {
        if in_teardown_child("update_preserves_incoming_binding_during_deferred_destruction") {
            check_incoming_binding_survives_collection(true);
        }
    }

    #[test]
    fn deferred_destruction_preserves_active_roots_and_pending_results() {
        use crate::{
            compiler::constants::ConstantMap,
            gc::Gc,
            rvals::{Custom, IntoSteelVal},
            steel_vm::vm::{StackFrame, VmCore},
            values::{
                closed::Heap,
                functions::{ByteCodeLambda, RootedInstructions},
            },
            SteelVal,
        };
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        if !in_teardown_child("deferred_destruction_preserves_active_roots_and_pending_results") {
            return;
        }

        struct CollectOnDrop {
            engine: Engine,
            calls: Arc<AtomicUsize>,
        }
        impl Custom for CollectOnDrop {}
        impl Drop for CollectOnDrop {
            fn drop(&mut self) {
                assert!(self.engine.virtual_machine.heap.try_lock().is_some());
                self.engine.run("(probe-gc)").unwrap();
                self.calls.fetch_add(1, Ordering::SeqCst);
            }
        }

        for allocation in 0..if cfg!(all(feature = "sync", feature = "biased")) {
            15
        } else {
            10
        } {
            let mut engine = Engine::new_raw_no_kernel();
            register_gc(&mut engine);
            // The collecting engine shares the heap but has none of the active VM's roots.
            let collector = engine.clone();
            let calls = Arc::new(AtomicUsize::new(0));
            let thread = &mut engine.virtual_machine;
            let values: Vec<_> = (0..9)
                .map(|i| {
                    SteelVal::HeapAllocated(
                        thread
                            .heap
                            .lock()
                            .allocate_without_collection(SteelVal::IntV(42 + i)),
                    )
                })
                .collect();
            let unrelated = thread
                .heap
                .lock()
                .allocate_without_collection(SteelVal::IntV(99));
            let frame = |capture: SteelVal, handler: SteelVal| {
                let mut frame = StackFrame::main().with_handler(handler);
                frame.set_function(Gc::new(ByteCodeLambda::new(
                    0,
                    vec![].into(),
                    0,
                    false,
                    vec![capture].into_iter().collect(),
                )));
                frame
            };
            thread.stack.push(values[0].clone());
            thread.thread_local_storage.push(values[1].clone());
            thread.current_frame = frame(values[2].clone(), values[3].clone());
            thread
                .stack_frames
                .push(frame(values[4].clone(), values[5].clone()));
            thread.insert_binding(thread.global_env.len(), values[6].clone());
            thread.constant_map = ConstantMap::from_vec(vec![values[7].clone()]);
            let mut ctx = VmCore {
                thread,
                constants: ConstantMap::from_vec(vec![values[8].clone()]),
                instructions: RootedInstructions::new(vec![].into()),
                ip: 0,
                sp: 0,
                pop_count: 1,
                depth: 0,
                root_spans: &[],
                return_value: None,
                is_native: false,
                result: None,
            };
            let probe = CollectOnDrop {
                engine: collector,
                calls: calls.clone(),
            }
            .into_steelval()
            .unwrap();
            if allocation < 5 {
                ctx.thread.heap.lock().released.push(probe);
            } else if allocation < 10 {
                let retained = Heap::retain_shared(vec![probe], &ctx.thread.heap);
                ctx.thread.heap.lock().released_retained.push(retained);
            } else {
                #[cfg(all(feature = "sync", feature = "biased"))]
                std::thread::spawn(move || drop(probe)).join().unwrap();
            }
            let result = match allocation % 5 {
                #[cfg(feature = "jit2")]
                0 => crate::steel_vm::vm::jit::box_handler_c(&mut ctx, SteelVal::IntV(100)),
                #[cfg(not(feature = "jit2"))]
                0 => ctx.make_box(SteelVal::IntV(100)),
                1 => ctx.make_mutable_vector(vec![SteelVal::IntV(100)]),
                2 => ctx.make_mutable_vector_iter([SteelVal::IntV(100)].into_iter()),
                3 => {
                    // Adopted copies are not reachable from the source value until rewritten.
                    let mut source = Heap::new();
                    let cell = source.allocate_without_collection(SteelVal::IntV(100));
                    let mut value = SteelVal::MutableVector(
                        source.allocate_vec_without_collection(vec![SteelVal::HeapAllocated(cell)]),
                    );
                    let root = value.as_rooted();
                    let cells = source.reached_cells(&value);
                    let adopted = ctx
                        .thread
                        .with_heap(Some(&ctx.constants), |_, heap| heap.adopt(cells));
                    assert!(adopted.rewrite(&mut value).is_empty());
                    drop(root);
                    let SteelVal::MutableVector(vector) = value else {
                        panic!("expected an adopted vector");
                    };
                    vector.get()[0].clone()
                }
                _ => {
                    ctx.thread.with_heap(Some(&ctx.constants), |_, _| {});
                    SteelVal::IntV(100)
                }
            };
            assert_eq!(calls.load(Ordering::SeqCst), 1);
            match result {
                SteelVal::HeapAllocated(cell) => assert_eq!(cell.get(), SteelVal::IntV(100)),
                SteelVal::MutableVector(vector) => {
                    assert_eq!(vector.get(), [SteelVal::IntV(100)]);
                }
                SteelVal::IntV(100) => {}
                _ => panic!("unexpected allocation result"),
            }
            for (i, value) in values.iter().enumerate() {
                let SteelVal::HeapAllocated(cell) = value else {
                    unreachable!();
                };
                assert_eq!(cell.get(), SteelVal::IntV(42 + i as isize), "root {i}");
            }
            assert_eq!(unrelated.get(), SteelVal::Void);
        }
    }

    #[test]
    fn garbage_collection_releases_discarded_native_values() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::sync::Arc;
        if !in_teardown_child("garbage_collection_releases_discarded_native_values") {
            return;
        }

        #[derive(Clone)]
        struct Probe {
            _owner: Arc<()>,
        }
        impl crate::rvals::Custom for Probe {}
        let count = Arc::new(());
        let factory = count.clone();
        let mut engine = Engine::new();
        engine.register_fn("probe-value", move || Probe {
            _owner: factory.clone(),
        });
        engine.run("(define live (probe-value)) (define (probe) (define value (probe-value)) (define (read) value) (set! value (probe-value)) (vector (read)) void)").unwrap();
        for _ in 0..1000 {
            engine
                .call_function_by_name_with_args("probe", vec![])
                .unwrap();
        }
        register_gc(&mut engine);
        engine
            .run(
                r#"
            (define (probe-cycles)
              (define rows (map (lambda (i) (hash "i" i "owner" (probe-value))) (range 100)))
              (define (walk i) (if (< i (length rows)) (walk (+ i 1)) void))
              (walk 0))
        "#,
            )
            .unwrap();
        for _ in 0..1000 {
            engine
                .call_function_by_name_with_args("probe-cycles", vec![])
                .unwrap();
        }
        assert!(
            Arc::strong_count(&count) < 10_000,
            "unreachable recursive captures must be collected during sustained callbacks"
        );
        engine.run("(probe-gc)").unwrap();
        assert_eq!(
            Arc::strong_count(&count),
            3,
            "only the live value and factory may retain the payload"
        );
        // Release the old value returned by set! before collecting it.
        engine.run("(set! live #f)").unwrap();
        engine.run("(probe-gc)").unwrap();
        assert_eq!(
            Arc::strong_count(&count),
            2,
            "discarded payloads must be released before heap slots are reused"
        );
    }

    #[test]
    fn list_equality_checks_shared_prefixes_with_different_tails() {
        let mut engine = Engine::new();
        engine.run("(define prefix (range 50)) (define a (append prefix '(50))) (define b (append prefix '(51)))").unwrap();
        for expression in [
            "(equal? prefix a)",
            "(equal? a b)",
            "(equal? (list a) (list b))",
            "(eq? prefix a)",
            "(eq? a b)",
            "(eq? (cdr a) (cdr b))",
            "(eq? a (cdr a))",
            "(eq? (cdr a) (cdr (cdr a)))",
            "(eqv? a b)",
        ] {
            assert_eq!(
                engine.run(expression).unwrap(),
                [crate::SteelVal::BoolV(false)],
                "{expression}"
            );
        }
        for expression in [
            "(equal? a (range 51))",
            "(eq? (cdr a) (cdr a))",
            "(eqv? (cdr a) (cdr a))",
            "(equal? (cdr a) (cdr a))",
        ] {
            assert_eq!(
                engine.run(expression).unwrap(),
                [crate::SteelVal::BoolV(true)],
                "{expression}"
            );
        }
    }

    #[test]
    fn equality_compares_pairs_of_nodes() {
        let mut engine = Engine::new();
        for constructor in [
            "list",
            "vector",
            "immutable-vector",
            "(lambda (x) (cons x 0))",
            "(lambda (x) (hash 'value x))",
        ] {
            engine
                .run(format!(
                    "(define a ({constructor} 1)) (define b ({constructor} 1)) (define c ({constructor} 2))"
                ))
                .unwrap();
            for (expression, expected) in [
                ("(equal? (list a a) (list c b))", false),
                ("(equal? (list c b) (list a a))", false),
                ("(equal? (list a a) (list b b))", true),
                ("(equal? (list b b) (list a a))", true),
            ] {
                assert_eq!(
                    engine.run(expression).unwrap(),
                    [crate::SteelVal::BoolV(expected)],
                    "{constructor}: {expression}"
                );
            }
        }
    }

    #[test]
    fn list_identity_preserves_repeated_cdr_sharing() {
        let mut engine = Engine::new();
        for size in [2, 4, 5, 16, 50] {
            engine.run(format!("(define xs (range {size}))")).unwrap();
            for expression in [
                "(eq? (cdr xs) (cdr xs))",
                "(eqv? (cdr xs) (cdr xs))",
                "(equal? (cdr xs) (cdr xs))",
                "(pair? (memq (cdr xs) (list (cdr xs))))",
                "(not (eq? xs (cdr xs)))",
            ] {
                assert_eq!(
                    engine.run(expression).unwrap(),
                    [crate::SteelVal::BoolV(true)],
                    "length {size}: {expression}"
                );
            }
        }
    }

    #[test]
    fn list_equality_terminates_on_cycles() {
        let mut engine = Engine::new();
        engine
            .run(
                r#"
                (define left (vector #f))
                (define right (vector #f))
                (vector-set! left 0 (list left 1))
                (vector-set! right 0 (list right 1))
                "#,
            )
            .unwrap();
        assert_eq!(
            engine.run("(equal? left right)").unwrap(),
            [crate::SteelVal::BoolV(true)]
        );
        engine.run("(vector-set! right 0 (list right 2))").unwrap();
        assert_eq!(
            engine.run("(equal? left right)").unwrap(),
            [crate::SteelVal::BoolV(false)]
        );
        engine
            .run(
                r#"
                (define left-box (box #f))
                (define right-box (box #f))
                (set-box! left-box (list left-box 1))
                (set-box! right-box (list right-box 1))
                "#,
            )
            .unwrap();
        assert_eq!(
            engine.run("(equal? left-box right-box)").unwrap(),
            [crate::SteelVal::BoolV(true)]
        );
        engine
            .run("(set-box! right-box (list right-box 2))")
            .unwrap();
        assert_eq!(
            engine.run("(equal? left-box right-box)").unwrap(),
            [crate::SteelVal::BoolV(false)]
        );
    }

    #[test]
    fn internal_initializer_returns_from_enclosing_function() {
        let mut engine = Engine::new();
        engine
            .run(
                r#"
                (define (example)
                  (define (helper) 1)
                  (define value (return! 9))
                  10)
                "#,
            )
            .unwrap();
        assert_eq!(engine.run("(example)").unwrap(), [crate::SteelVal::IntV(9)]);
        for body in [
            "(let ((x 1)) (return! 9)) 10",
            "(begin (define (helper) 1) (define value (return! 9)) value) 10",
        ] {
            let result = engine.run(format!("((lambda () {body}))")).unwrap();
            assert_eq!(result.last(), Some(&crate::SteelVal::IntV(9)), "{body}");
        }
    }

    #[test]
    fn let_family_preserves_returns_and_bindings() {
        let mut engine = Engine::new();
        for form in ["let*", "letrec", "letrec*"] {
            for bindings in ["()", "((x 1))", "((x 1) (y (+ x 1)))"] {
                let source = format!("((lambda () ({form} {bindings} (let () (return! 9))) 10))");
                assert_eq!(
                    engine.run(source.clone()).unwrap().last(),
                    Some(&crate::SteelVal::IntV(9)),
                    "{source}"
                );
            }
            for body in [
                format!("({form} ((x 1) (y (return! 9))) y)"),
                format!("({form} () ({form} ((x 1)) (return! 9)))"),
            ] {
                let source = format!("((lambda () {body} 10))");
                assert_eq!(
                    engine.run(source.clone()).unwrap().last(),
                    Some(&crate::SteelVal::IntV(9)),
                    "{source}"
                );
            }
            let source = format!(
                "((lambda () ({form} ((x ((lambda () (return! 9))))) ((lambda () (return! x)))) 10))"
            );
            assert_eq!(
                engine.run(source.clone()).unwrap().last(),
                Some(&crate::SteelVal::IntV(10)),
                "{source}"
            );
            let source = format!(
                "(let ((effects '())) ({form} ((x (begin (set! effects (cons 1 effects)) 1)) (y (begin (set! effects (cons 2 effects)) (+ x 1)))) (list x y effects)))"
            );
            assert_eq!(
                engine
                    .run(source.clone())
                    .unwrap()
                    .last()
                    .unwrap()
                    .to_string(),
                "(1 2 (2 1))",
                "{source}"
            );
        }
        for form in ["letrec", "letrec*"] {
            let source = format!(
                "({form} ((even? (lambda (n) (if (= n 0) #t (odd? (- n 1))))) (odd? (lambda (n) (if (= n 0) #f (even? (- n 1)))))) (even? 10))"
            );
            assert_eq!(
                engine.run(source.clone()).unwrap().last(),
                Some(&crate::SteelVal::BoolV(true)),
                "{source}"
            );
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn garbage_collection_preserves_shared_graph() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run(
                "(define (wrap n node) (if (= n 0) node (wrap (- n 1) (list node node))))
             (define graph (wrap 22 (box 42)))
             (probe-gc)",
            )
            .unwrap();
        let result = engine
            .run(
                "(define (leaf n node) (if (= n 0) (unbox node) (leaf (- n 1) (car node))))
             (leaf 22 graph)",
            )
            .unwrap();
        assert_eq!(result.last(), Some(&crate::SteelVal::IntV(42)));
    }

    #[test]
    fn internal_initializers_preserve_order_dependencies_and_lambda_returns() {
        let mut engine = Engine::new();
        let result = engine
            .run(
                r#"
                (define effects '())
                (define (record value)
                  (set! effects (append effects (list value)))
                  value)
                (define (example)
                  (define (even-local? n) (if (= n 0) #t (odd-local? (- n 1))))
                  (record 1)
                  (define first (record 2))
                  (record 3)
                  (define second (record (+ first 2)))
                  (define (odd-local? n) (if (= n 0) #f (even-local? (- n 1))))
                  (define third ((lambda () (let ((x 5)) (return! x)) 99)))
                  (define fourth ((lambda () ((lambda (x) x) (return! 6)))))
                  (list first second third fourth (even-local? 10) effects))
                (example)
                "#,
            )
            .unwrap();
        assert_eq!(
            result.last().unwrap().to_string(),
            "(2 4 5 6 #true (1 2 3 4))"
        );
    }

    #[cfg(feature = "sync")]
    fn check_other_thread_allocations(constructor: &str, reader: &str, recycle: bool) {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::{
            panic::{catch_unwind, AssertUnwindSafe},
            time::Duration,
        };

        let (ready_tx, ready_rx) = crossbeam_channel::bounded(1);
        let (release_tx, release_rx) = crossbeam_channel::bounded(1);
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine.register_fn("probe-block", move || {
            ready_tx.send(()).unwrap();
            release_rx.recv_timeout(Duration::from_secs(10)).is_ok()
        });
        let worker = engine
            .run(format!(
                r#"
                (spawn-native-thread
                  (lambda ()
                    (define retained (map {constructor} (range 200)))
                    (and (probe-block)
                         (equal? (map {reader} retained) (range 200)))))
                "#,
            ))
            .unwrap()
            .pop()
            .unwrap();

        // Join the worker even if incorrect free-slot accounting panics during allocation.
        let allocation = catch_unwind(AssertUnwindSafe(|| {
            engine
                .virtual_machine
                .enter_safepoint(|_| ready_rx.recv_timeout(Duration::from_secs(10)))
                .unwrap();
            if recycle {
                for _ in 0..150 {
                    engine.run("(define shadowed 0)").unwrap();
                }
            } else {
                engine.run("(probe-gc)").unwrap();
            }
            engine
                .run(format!(
                    r#"
                    (define added (map {constructor} (range 1000)))
                    (equal? (map {reader} added) (range 1000))
                    "#,
                ))
                .unwrap()
        }));
        let _ = release_tx.send(());
        engine.virtual_machine.synchronizer.resume_threads();
        let retained = engine
            .virtual_machine
            .enter_safepoint(|_| join_thread(&worker));

        assert_eq!(
            allocation.unwrap().last(),
            Some(&crate::SteelVal::BoolV(true))
        );
        assert_eq!(retained.unwrap(), crate::SteelVal::BoolV(true));
    }

    #[cfg(feature = "sync")]
    #[test]
    fn recycling_preserves_values_on_worker_stacks() {
        check_other_thread_allocations("box", "unbox", true);
        check_other_thread_allocations("vector", "(lambda (v) (vector-ref v 0))", true);
    }

    #[cfg(feature = "sync")]
    #[test]
    fn other_thread_roots_count_toward_box_allocations() {
        check_other_thread_allocations("box", "unbox", false);
    }

    #[cfg(feature = "sync")]
    #[test]
    fn other_thread_roots_count_toward_vector_allocations() {
        check_other_thread_allocations("vector", "(lambda (value) (vector-ref value 0))", false);
    }

    #[cfg(feature = "sync")]
    #[test]
    fn other_thread_finalizers_record_eligibility_before_retention() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::{
            panic::{catch_unwind, AssertUnwindSafe},
            time::Duration,
        };

        let (ready_tx, ready_rx) = crossbeam_channel::bounded(1);
        let (release_tx, release_rx) = crossbeam_channel::bounded(1);
        let (result_tx, result_rx) = crossbeam_channel::bounded(1);
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine.register_fn("probe-block", move || {
            ready_tx.send(()).unwrap();
            release_rx.recv_timeout(Duration::from_secs(10)).is_ok()
        });
        engine.register_fn("probe-result", move |value: isize| {
            result_tx.send(value).unwrap();
            value
        });
        let worker = engine
            .run(
                r#"
                (define executor (make-will-executor))
                (let ((target (box #f)))
                  (set-box! target (list target 42))
                  (will-register executor target (lambda (value) (car (cdr (unbox value))))))
                (let ((captured executor))
                  (spawn-native-thread
                    (lambda ()
                      (and (probe-block)
                           (probe-result (will-execute captured))))))
                "#,
            )
            .unwrap()
            .pop()
            .unwrap();

        let collection = catch_unwind(AssertUnwindSafe(|| {
            engine
                .virtual_machine
                .enter_safepoint(|_| ready_rx.recv_timeout(Duration::from_secs(10)))
                .unwrap();
            engine.run("(probe-gc) (probe-gc)").unwrap();
        }));
        engine.virtual_machine.synchronizer.resume_threads();
        let _ = release_tx.send(());
        // Registration wakes will-execute even if GC failed to make the first will eligible.
        engine
            .run("(will-register executor (box 99) (lambda (value) (unbox value)))")
            .unwrap();
        let result = engine
            .virtual_machine
            .enter_safepoint(|_| result_rx.recv_timeout(Duration::from_secs(10)));
        let joined = engine
            .virtual_machine
            .enter_safepoint(|_| join_thread(&worker));

        collection.unwrap();
        assert_eq!(result.unwrap(), 42);
        assert_eq!(joined.unwrap(), crate::SteelVal::IntV(42));
    }

    #[cfg(feature = "sync")]
    #[test]
    fn global_collection_handles_finalizers_capturing_their_executor() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run(
                r#"
                (define key-value (box 17))
                (define callback-value (box 25))
                (define executor (make-will-executor))
                (let ((captured executor))
                  (will-register executor
                    (box (lambda () (unbox key-value)))
                    (lambda (key)
                      (if (eq? captured executor)
                          (+ ((unbox key)) (unbox callback-value))
                          0))))
                "#,
            )
            .unwrap();
        engine
            .run("(define key-value (box 0)) (define callback-value (box 0))")
            .unwrap();

        for _ in 0..150 {
            engine.run("(define shadowed 0)").unwrap();
        }

        engine.run("(probe-gc)").unwrap();
        assert_eq!(
            engine.run("(will-execute executor)").unwrap(),
            [crate::SteelVal::IntV(42)]
        );
    }

    #[cfg(feature = "sync")]
    #[test]
    fn finalizers_retain_heap_payloads_across_collections() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run("(define executor (make-will-executor))")
            .unwrap();
        for (payload, reader, expected) in [
            ("(vector 10 20)", "(vector-ref value 1)", 20),
            ("(box 42)", "(unbox value)", 42),
            (
                "(list (box (vector 1 (box 2))))",
                "(unbox (vector-ref (unbox (car value)) 1))",
                2,
            ),
            (
                "(vector (box (vector 7)))",
                "(vector-ref (unbox (vector-ref value 0)) 0)",
                7,
            ),
        ] {
            engine
                .run(format!(
                    "(will-register executor {payload} (lambda (value) (probe-gc) {reader}))"
                ))
                .unwrap();
            for _ in 0..3 {
                engine
                    .run("(probe-gc) (map (lambda (i) (box (vector i))) (range 1000)) void")
                    .unwrap();
            }
            assert_eq!(
                engine.run("(will-execute executor)").unwrap(),
                [crate::SteelVal::IntV(expected)],
                "{payload}"
            );
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn finalizers_retain_callbacks_and_release_executed_payloads() {
        use crate::steel_vm::register_fn::RegisterFn;
        use std::sync::Arc;

        #[derive(Clone)]
        struct Probe {
            _owner: Arc<()>,
        }
        impl crate::rvals::Custom for Probe {}

        let count = Arc::new(());
        let factory = count.clone();
        let mut engine = Engine::new();
        engine.register_fn("probe-value", move || Probe {
            _owner: factory.clone(),
        });
        register_gc(&mut engine);
        engine
            .run(
                r#"
                (define executor (make-will-executor))
                (define live (box (vector (probe-value) 17)))
                (let ((capture (box (vector (probe-value) 25))))
                  (will-register executor live
                    (lambda (value)
                      (probe-gc)
                      (+ (vector-ref (unbox value) 1)
                         (vector-ref (unbox capture) 1)))))
                (probe-gc)
                "#,
            )
            .unwrap();
        assert_eq!(Arc::strong_count(&count), 4);
        // Release the old value returned by set! before testing will eligibility.
        engine.run("(set! live #f)").unwrap();
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(Arc::strong_count(&count), 4);
        assert_eq!(
            engine.run("(will-execute executor)").unwrap(),
            [crate::SteelVal::IntV(42)]
        );
        engine.run("(probe-gc)").unwrap();
        assert_eq!(Arc::strong_count(&count), 2);
    }

    #[cfg(feature = "sync")]
    #[test]
    fn finalizers_record_eligibility_before_retaining_other_wills() {
        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run(
                r#"
                (define first (make-will-executor))
                (define second (make-will-executor))
                (let ((payload (box 42)))
                  (will-register first payload unbox)
                  (will-register second (vector payload)
                    (lambda (value) (unbox (vector-ref value 0)))))
                (probe-gc)
                (probe-gc)
                "#,
            )
            .unwrap();
        for executor in ["first", "second"] {
            assert_eq!(
                engine.run(format!("(will-execute {executor})")).unwrap(),
                [crate::SteelVal::IntV(42)]
            );
        }
    }
}
