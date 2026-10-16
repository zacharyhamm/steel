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
mod embedding_regressions {
    use crate::steel_vm::engine::Engine;

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
    fn cyclic_struct_properties_keep_heap_values_alive() {
        use crate::{gc::Gc, values::structs::VTable, SteelVal};

        let mut engine = Engine::new();
        register_gc(&mut engine);
        engine
            .run("(struct holder ()) (define owner (holder))")
            .unwrap();
        let SteelVal::CustomStruct(owner) = engine.extract_value("owner").unwrap() else {
            panic!("expected a struct");
        };
        let original_properties = owner.properties();
        let mut properties = (*original_properties).clone();
        let payload = engine.run("(box 42)").unwrap().pop().unwrap();
        properties.insert(payload, SteelVal::CustomStruct(owner.clone()));
        VTable::set_entry(&owner.type_descriptor, None, Gc::new(properties));
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(
            owner
                .properties()
                .keys()
                .find_map(SteelVal::as_box_to_inner),
            Some(SteelVal::IntV(42))
        );
        VTable::set_entry(&owner.type_descriptor, None, original_properties);
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
        use crate::steel_vm::vm::threads::{thread_finished, thread_join};
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
            thread_join(&worker).unwrap(),
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
            assert_eq!(Arc::strong_count(&count), 2);
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn completed_thread_results_keep_originating_heap_alive() {
        use crate::steel_vm::vm::threads::{thread_finished, thread_join};
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

        let mut collector = Engine::new_raw_no_kernel();
        register_gc(&mut collector);
        for join in [false, true] {
            let mut engine = Engine::new_raw_no_kernel();
            crate::steel_vm::primitives::register_builtin_modules(&mut engine, true);
            let heap = Arc::downgrade(&engine.virtual_machine.heap);
            let worker = engine
                .run(
                    "(require-builtin steel/meta)
                     (require-builtin steel/threads)
                     (spawn-native-thread (lambda () (box 42)))",
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
            drop(engine);
            assert_eq!(
                heap.strong_count(),
                1,
                "the pending result must own its heap"
            );
            collector.run("(probe-gc) (probe-gc)").unwrap();

            if join {
                // Keep the heap alive while inspecting the unrooted join result.
                let heap = heap.upgrade().unwrap();
                let joined = thread_join(&worker).unwrap();
                assert_eq!(joined.as_box_to_inner(), Some(crate::SteelVal::IntV(42)));
                drop(joined);
                assert_eq!(Arc::strong_count(&heap), 1);
                assert!(thread_join(&worker).is_err());
            }
            drop(worker);
            assert!(heap.upgrade().is_none());
            collector.run("(probe-gc) (probe-gc)").unwrap();
        }
    }

    #[cfg(feature = "sync")]
    #[test]
    fn engine_teardown_releases_heap_stored_thread_handles() {
        use crate::steel_vm::{register_fn::RegisterFn, vm::threads::thread_finished};
        use std::{
            sync::Arc,
            time::{Duration, Instant},
        };

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
            // shortcut: keep probe owners alive until biased RC can reclaim exited workers' values.
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
    fn garbage_collection_releases_discarded_native_values() {
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
        engine.run("(set! live #f) (probe-gc)").unwrap();
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
    fn check_other_thread_allocations(constructor: &str, reader: &str) {
        use crate::steel_vm::{register_fn::RegisterFn, vm::threads::thread_join};
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
            engine
                .run(format!(
                    r#"
                    (probe-gc)
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
            .enter_safepoint(|_| thread_join(&worker));

        assert_eq!(
            allocation.unwrap().last(),
            Some(&crate::SteelVal::BoolV(true))
        );
        assert_eq!(retained.unwrap(), crate::SteelVal::BoolV(true));
    }

    #[cfg(feature = "sync")]
    #[test]
    fn other_thread_roots_count_toward_box_allocations() {
        check_other_thread_allocations("box", "unbox");
    }

    #[cfg(feature = "sync")]
    #[test]
    fn other_thread_roots_count_toward_vector_allocations() {
        check_other_thread_allocations("vector", "(lambda (value) (vector-ref value 0))");
    }

    #[cfg(feature = "sync")]
    #[test]
    fn other_thread_finalizers_record_eligibility_before_retention() {
        use crate::steel_vm::{register_fn::RegisterFn, vm::threads::thread_join};
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
            .enter_safepoint(|_| thread_join(&worker));

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
        engine.run("(set! live #f) (probe-gc) (probe-gc)").unwrap();
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
