use core::cell::RefCell;
use std::collections::HashSet;

#[cfg(feature = "sync")]
use std::sync::Mutex;

#[cfg(feature = "sync")]
use crate::rvals::cycles::BreadthFirstSearchSteelValReferenceVisitor2;

#[cfg(feature = "sync")]
use crate::rvals::SteelValPointer;

use crate::{
    compiler::{constants::ConstantMap, map::SymbolMap},
    gc::{
        shared::{MutContainer, ShareableMut, StandardShared, StandardSharedMut, WeakShared},
        GcMut,
    },
    rvals::{
        AsRefSteelVal, Custom, IntoSteelVal, OpaqueIterator, RestArgsIter, SteelComplex,
        SteelVector,
    },
    steel_vm::vm::{Continuation, ContinuationMark, HeapHandle, Synchronizer, VmCore},
    values::lists::List,
    SteelErr,
};

#[cfg(feature = "sync")]
use crate::steel_vm::vm::apply;

#[cfg(feature = "sync")]
use crossbeam_channel::{Receiver, Sender};

use num_bigint::BigInt;
use num_rational::{BigRational, Rational32};

#[cfg(feature = "sync")]
use once_cell::sync::Lazy;

use steel_gen::OpCode;

use crate::{
    gc::{unsafe_erased_pointers::OpaqueReference, Gc},
    rvals::{
        cycles::BreadthFirstSearchSteelValVisitor, BoxedAsyncFunctionSignature, CustomType,
        FunctionSignature, FutureResult, MutFunctionSignature, SteelHashMap, SteelHashSet,
        SteelString, Syntax,
    },
    steel_vm::vm::BuiltInSignature,
    values::functions::ByteCodeLambda,
    SteelVal,
};

use super::{
    functions::BoxedDynFunction,
    lazy_stream::LazyStream,
    port::SteelPort,
    structs::{struct_function_descriptor, StructTypeDescriptor, UserDefinedStruct, VTable},
    transducers::{Reducer, ReducerFunc, Transducer, Transducers},
};

#[cfg(feature = "sync")]
use super::lists::Pair;

#[cfg(feature = "sync")]
use super::Vector;

#[derive(Default)]
pub struct GlobalSlotRecycler<'a> {
    // Use a hashset to check for free slots.
    // The idea here is that a collection will traverse
    // all active values (excluding roots with this index)
    // and we'll check to make sure these are reachable.
    //
    // If the values are eventually reachable, then we can keep
    // iterating until this is completely drained.
    //
    // If we reach the end of our iteration and this isn't
    // drained, whatever is left is now freeable, and we can make
    // this as free in the symbol map
    slots: HashSet<usize>,

    queue: Vec<SteelVal>,
    visited: rustc_hash::FxHashSet<usize>,
    struct_types: ReachedStructTypes,

    // While tracing registered roots, the functions whose closures keep their global slots.
    // Roots can hold other engines' closures, which refer to their own engines' slots.
    rooted_functions: Option<&'a rustc_hash::FxHashSet<u32>>,

    // Candidate slots a traced closure refers to. Their values are traced in turn, since a
    // kept slot's value can refer to other candidates.
    kept: Vec<usize>,

    // Every traversed value. A copy can outlive its source once another thread replaces
    // it, so its destructor runs after the heap and environment are unlocked.
    released: Vec<SteelVal>,

    #[cfg(feature = "sync")]
    will_executors: Vec<GcMut<Box<dyn CustomType>>>,
}

impl<'a> GlobalSlotRecycler<'a> {
    /// Returns the traversed values, to drop once the heap and environment are unlocked.
    #[must_use]
    pub fn free_shadowed_rooted_values(
        roots: &mut [SteelVal],
        symbol_map: &mut SymbolMap,
        function_ids: &'a rustc_hash::FxHashSet<u32>,
        heap: &mut Heap,
    ) -> Vec<SteelVal> {
        let mut recycler = GlobalSlotRecycler::default();

        recycler.recycle(roots, symbol_map, function_ids, heap)
    }

    // TODO:
    // Take the global roots, without the shadowed values, and iterate over them,
    // push the values back, visit, mark visited, move on.
    /// `function_ids` are the functions generated for these global slots. Returns the traversed
    /// values, to drop once the heap and environment are unlocked.
    #[must_use]
    pub fn recycle(
        &mut self,
        roots: &mut [SteelVal],
        symbol_map: &mut SymbolMap,
        function_ids: &'a rustc_hash::FxHashSet<u32>,
        _heap: &mut Heap,
    ) -> Vec<SteelVal> {
        self.slots.clear();
        self.queue.clear();
        self.kept.clear();
        self.visited.clear();
        self.struct_types.clear();
        #[cfg(feature = "sync")]
        self.will_executors.clear();

        // TODO: Right now, after one pass, we'll ignore it forever.
        // we should move it to another stage that we check later.
        for slot in symbol_map
            .free_list
            .shadowed_slots
            .drain(..)
            .chain(symbol_map.free_list.lambda_lifted.drain(..))
        {
            self.slots.insert(slot);
        }

        for (index, root) in roots.iter().enumerate() {
            if !self.slots.contains(&index) {
                self.push_back(root.clone());
            }
        }
        self.visit();
        self.visit_kept(roots);

        // Values reached first through a registered root keep only this compiler's slots.
        let visited = core::mem::take(&mut self.visited);
        let struct_types = core::mem::take(&mut self.struct_types);
        self.rooted_functions = Some(function_ids);
        for root in persistent_roots_snapshot() {
            self.push_back(root);
        }
        self.visit();
        self.rooted_functions = None;
        self.visited = visited;
        self.struct_types = struct_types;
        self.visit_kept(roots);

        // An early exit must not leave roots or visited cells for the next pass.
        self.released.append(&mut self.queue);
        self.kept.clear();
        self.visited.clear();
        self.struct_types.clear();
        #[cfg(feature = "sync")]
        self.will_executors.clear();

        for index in self.slots.drain() {
            if index < roots.len() {
                symbol_map.free_list.free_list.push(index);
                self.released
                    .push(core::mem::replace(&mut roots[index], SteelVal::Void));
            }
        }
        core::mem::take(&mut self.released)
    }

    // Trace the values of the candidate slots that traced closures refer to. They are this
    // engine's globals, so their closures keep their slots whichever compiler made them.
    fn visit_kept(&mut self, roots: &[SteelVal]) {
        while let Some(index) = self.kept.pop() {
            if let Some(value) = roots.get(index) {
                self.push_back(value.clone());
                self.visit();
            }
        }
    }
}

#[test]
fn recycling_preserves_heap_state_and_clears_pending_traversal() {
    use crate::{core::instructions::DenseInstruction, steel_vm::engine::Engine};

    let mut engine = Engine::new_raw_no_kernel();
    let thread = &mut engine.virtual_machine;
    let mut heap = thread.heap.lock();
    let value = heap.allocate_without_collection(SteelVal::IntV(42));
    let vector = heap.allocate_vec_without_collection(vec![SteelVal::HeapAllocated(value.clone())]);
    let registered = SteelVal::MutableVector(vector.clone()).as_rooted();
    let constant = heap.allocate_without_collection(SteelVal::IntV(43));
    thread
        .constant_map
        .add(SteelVal::HeapAllocated(constant.clone()));
    let tls = heap.allocate_vec_without_collection(vec![SteelVal::IntV(44)]);
    thread
        .thread_local_storage
        .push(SteelVal::MutableVector(tls.clone()));
    let memory_flags: Vec<_> = heap
        .memory_free_list
        .elements
        .iter()
        .map(|x| x.read().reachable)
        .collect();
    let vector_flags: Vec<_> = heap
        .vector_free_list
        .elements
        .iter()
        .map(|x| x.read().reachable)
        .collect();
    let memory_count = heap.memory_free_list.alloc_count;
    let vector_count = heap.vector_free_list.alloc_count;
    let closure = SteelVal::Closure(Gc::new(ByteCodeLambda::new(
        0,
        vec![DenseInstruction::new(
            OpCode::PUSH,
            crate::core::instructions::u24::from_usize(0),
        )]
        .into(),
        0,
        false,
        Default::default(),
    )));
    let functions = Default::default();
    let mut recycler = GlobalSlotRecycler::default();
    let mut symbols = SymbolMap::new();
    // No candidates, a complete pass, and a pass that exits with pending roots.
    for candidate in [None, Some(1), Some(0), None] {
        let mut roots = [
            SteelVal::IntV(1),
            SteelVal::IntV(2),
            SteelVal::ListV(vec![closure.clone()].into()),
            closure.clone(),
        ];
        symbols.free_list.shadowed_slots.extend(candidate);
        drop(recycler.recycle(&mut roots, &mut symbols, &functions, &mut heap));
        assert_eq!(roots[0], SteelVal::IntV(1));
        assert_eq!(
            roots[1],
            if candidate == Some(1) {
                SteelVal::Void
            } else {
                SteelVal::IntV(2)
            }
        );
        assert!(recycler.queue.is_empty());
        assert!(recycler.visited.is_empty());
        assert_eq!(
            heap.memory_free_list
                .elements
                .iter()
                .map(|x| x.read().reachable)
                .collect::<Vec<_>>(),
            memory_flags
        );
        assert_eq!(
            heap.vector_free_list
                .elements
                .iter()
                .map(|x| x.read().reachable)
                .collect::<Vec<_>>(),
            vector_flags
        );
        assert_eq!(heap.memory_free_list.alloc_count, memory_count);
        assert_eq!(heap.vector_free_list.alloc_count, vector_count);
    }
    for _ in 0..1024 {
        heap.allocate_without_collection(SteelVal::Void);
        heap.allocate_vec_without_collection(vec![]);
    }
    assert_eq!(value.get(), SteelVal::IntV(42));
    assert_eq!(vector.get(), vec![SteelVal::HeapAllocated(value)]);
    assert_eq!(constant.get(), SteelVal::IntV(43));
    assert_eq!(tls.get(), vec![SteelVal::IntV(44)]);
    drop(heap);
    drop(registered);
}

#[cfg(test)]
struct DirectHeapChildren {
    value: HeapRef<SteelVal>,
    vector: HeapRef<Vec<SteelVal>>,
}

#[cfg(test)]
impl Custom for DirectHeapChildren {
    fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
        if let Some(value) = self.value.inner.upgrade() {
            context.mark_heap_reference(&value);
        }
        if let Some(vector) = self.vector.inner.upgrade() {
            context.mark_heap_vector(&vector);
        }
    }
}

#[test]
fn recycling_traces_registered_strong_box_cycles_once_per_pass() {
    let boxed = Gc::new_mut(SteelVal::Void);
    *boxed.write() = SteelVal::Boxed(boxed.clone());
    let mut recycler = GlobalSlotRecycler::default();
    recycler.visit_boxed_value(boxed.clone());
    let Some(SteelVal::Boxed(revisited)) = recycler.pop_front() else {
        panic!("the first visit must trace the box's value");
    };
    recycler.visit_boxed_value(revisited);
    *boxed.write() = SteelVal::Void;
    // Fail before running a full traversal if a cycle would requeue itself forever.
    assert!(recycler.queue.is_empty());

    let registered = SteelVal::Boxed(boxed.clone()).as_rooted();
    let mut heap = Heap::new();
    let mut symbols = SymbolMap::new();
    let functions = Default::default();
    for _ in 0..2 {
        *boxed.write() = SteelVal::Boxed(boxed.clone());
        let mut roots = [SteelVal::IntV(42)];
        symbols.free_list.shadowed_slots.push(0);
        drop(recycler.recycle(&mut roots, &mut symbols, &functions, &mut heap));
        *boxed.write() = SteelVal::Void;
        assert_eq!(roots, [SteelVal::Void]);
        assert_eq!(symbols.free_list.free_list.pop(), Some(0));
        assert!(recycler.queue.is_empty());
        assert!(recycler.visited.is_empty());
    }
    drop(registered);
}

#[test]
fn recycling_traces_registered_closures_and_custom_heap_cycles() {
    use crate::core::instructions::DenseInstruction;

    let mut heap = Heap::new();
    // An id no compiled function has, so roots from concurrent tests cannot keep it.
    let id = u32::MAX;
    let closure = SteelVal::Closure(Gc::new(ByteCodeLambda::new(
        id,
        vec![DenseInstruction::new(
            OpCode::PUSH,
            crate::core::instructions::u24::from_usize(0),
        )]
        .into(),
        0,
        false,
        Default::default(),
    )));
    let value = heap.allocate_without_collection(closure);
    let vector = heap.allocate_vec_without_collection(vec![]);
    let custom = DirectHeapChildren {
        value: value.clone(),
        vector: vector.clone(),
    }
    .into_steelval()
    .unwrap();
    vector.set_interior_mut(vec![custom.clone()]);
    let registered = custom.as_rooted();
    let functions = [id].into_iter().collect();
    let mut recycler = GlobalSlotRecycler::default();
    let mut symbols = SymbolMap::new();
    let mut roots = [SteelVal::IntV(42), SteelVal::IntV(99)];
    for _ in 0..2 {
        symbols.free_list.shadowed_slots.extend([0, 1]);
        drop(recycler.recycle(&mut roots, &mut symbols, &functions, &mut heap));
        assert_eq!(roots, [SteelVal::IntV(42), SteelVal::Void]);
        assert!(value.strong_ptr().read().reachable);
        assert!(vector.strong_ptr().read().reachable);
    }
    vector.set_interior_mut(vec![]);
    drop(registered);
}

#[test]
fn recycling_keeps_slots_only_for_rooted_closures_of_this_compiler() {
    use crate::core::instructions::{u24, DenseInstruction};

    // Ids no compiled function has, so roots from concurrent tests cannot keep these slots.
    const OWNED: u32 = u32::MAX - 1;
    const FOREIGN: u32 = u32::MAX - 2;
    let closure = |id, slot| {
        SteelVal::Closure(Gc::new(ByteCodeLambda::new(
            id,
            vec![DenseInstruction::new(OpCode::PUSH, u24::from_usize(slot))].into(),
            0,
            false,
            Default::default(),
        )))
    };
    let rooted = [closure(OWNED, 0), closure(FOREIGN, 1)].map(|closure| closure.as_rooted());
    let functions = [OWNED].into_iter().collect();
    let mut heap = Heap::new();
    let mut symbols = SymbolMap::new();
    // A global's closure keeps its slot whichever compiler generated it.
    let mut roots = [
        SteelVal::IntV(0),
        SteelVal::IntV(1),
        SteelVal::IntV(2),
        closure(FOREIGN, 2),
    ];
    symbols.free_list.shadowed_slots.extend([0, 1, 2]);
    let released = GlobalSlotRecycler::free_shadowed_rooted_values(
        &mut roots,
        &mut symbols,
        &functions,
        &mut heap,
    );
    assert_eq!(
        roots[..3],
        [SteelVal::IntV(0), SteelVal::Void, SteelVal::IntV(2)]
    );
    assert_eq!(symbols.free_list.free_list, [1]);
    // The freed slot's value is released with the traversed values.
    assert!(released.contains(&SteelVal::IntV(1)));
    drop(rooted);
}

#[test]
fn recycling_revisits_filtered_roots_through_kept_globals() {
    use crate::core::instructions::{u24, DenseInstruction};

    struct Child(SteelVal);
    impl Custom for Child {
        fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
            context.push_back(self.0.clone());
        }
    }

    const OWNED: u32 = u32::MAX - 3;
    const FOREIGN: u32 = u32::MAX - 4;
    let closure = |id, slot| {
        SteelVal::Closure(Gc::new(ByteCodeLambda::new(
            id,
            vec![DenseInstruction::new(OpCode::PUSH, u24::from_usize(slot))].into(),
            0,
            false,
            Default::default(),
        )))
    };
    let descriptor = VTable::new_entry("recycler-property".into(), None, None);
    let properties = [(SteelVal::SymbolV("#:child".into()), closure(FOREIGN, 1))]
        .into_iter()
        .collect();
    VTable::set_entry(&descriptor, None, Gc::new(properties));
    let shared_values = [
        SteelVal::Boxed(Gc::new_mut(closure(FOREIGN, 1))),
        Child(closure(FOREIGN, 1)).into_steelval().unwrap(),
        SteelVal::HashMapV(
            Gc::new(
                [(SteelVal::IntV(0), closure(FOREIGN, 1))]
                    .into_iter()
                    .collect::<crate::values::HashMap<_, _>>(),
            )
            .into(),
        ),
        descriptor.into_steelval().unwrap(),
    ];
    let functions = [OWNED].into_iter().collect();
    let mut recycler = GlobalSlotRecycler::default();
    let mut heap = Heap::new();
    let mut symbols = SymbolMap::new();
    for shared in shared_values {
        let registered =
            SteelVal::ListV(vec![closure(OWNED, 0), shared.clone()].into()).as_rooted();
        for _ in 0..2 {
            let mut roots = [shared.clone(), SteelVal::IntV(42), SteelVal::IntV(99)];
            symbols.free_list.shadowed_slots.extend([0, 1, 2]);
            drop(recycler.recycle(&mut roots, &mut symbols, &functions, &mut heap));
            assert_eq!(roots[0], shared);
            assert_eq!(roots[1..], [SteelVal::IntV(42), SteelVal::Void]);
            assert_eq!(symbols.free_list.free_list, [2]);
            symbols.free_list.free_list.clear();
        }
        drop(registered);
    }
    VTable::set_entry(&descriptor, None, Gc::new(Default::default()));
}

#[test]
fn global_slot_recycling_traces_receiver_cycles_once_per_pass() {
    use crate::steel_vm::{
        engine::Engine,
        vm::threads::{channel_send, Channels},
    };
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    struct VisitCount(Arc<AtomicUsize>);
    impl Custom for VisitCount {
        fn gc_visit_children(&self, _context: &mut MarkAndSweepContext) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    let count = Arc::new(AtomicUsize::new(0));
    let channels = Channels::new();
    let receiver = channels.receiver();
    let payload = VisitCount(count.clone()).into_steelval().unwrap();
    channel_send(&channels.sender(), receiver.clone()).unwrap();
    channel_send(&channels.sender(), payload.clone()).unwrap();

    let functions = Default::default();
    let mut recycler = GlobalSlotRecycler::default();
    let mut symbol_map = SymbolMap::new();
    let mut heap = Heap::new();
    let mut roots = [receiver.clone(), SteelVal::Void];
    for pass in 1..=2 {
        roots[1] = SteelVal::IntV(42);
        symbol_map.free_list.shadowed_slots.push(1);
        drop(recycler.recycle(&mut roots, &mut symbol_map, &functions, &mut heap));
        assert_eq!(roots[1], SteelVal::Void);
        assert_eq!(symbol_map.free_list.free_list.pop(), Some(1));
        assert_eq!(count.load(Ordering::SeqCst), pass);
    }

    let mut engine = Engine::new();
    let receive = engine
        .run("(lambda (receiver) (channel/try-recv receiver))")
        .unwrap()
        .pop()
        .unwrap();
    for expected in [receiver.clone(), payload] {
        assert_eq!(
            engine
                .call_function_with_args(receive.clone(), vec![receiver.clone()])
                .unwrap(),
            expected
        );
    }
}

impl BreadthFirstSearchSteelValVisitor for GlobalSlotRecycler<'_> {
    type Output = ();

    fn default_output(&mut self) -> Self::Output {}

    fn pop_front(&mut self) -> Option<SteelVal> {
        self.queue.pop()
    }

    fn visit(&mut self) -> Self::Output {
        use SteelVal::*;

        while let Some(value) = self.pop_front() {
            self.released.push(value.clone());
            if self.slots.is_empty() {
                return;
            }

            match value {
                Closure(c) => self.visit_closure(c),
                BoolV(b) => self.visit_bool(b),
                NumV(n) => self.visit_float(n),
                IntV(i) => self.visit_int(i),
                Rational(x) => self.visit_rational(x),
                BigRational(x) => self.visit_bigrational(x),
                BigNum(b) => self.visit_bignum(b),
                Complex(x) => self.visit_complex(x),
                CharV(c) => self.visit_char(c),
                VectorV(v) => self.visit_immutable_vector(v),
                Void => self.visit_void(),
                StringV(s) => self.visit_string(s),
                FuncV(f) => self.visit_function_pointer(f),
                SymbolV(s) => self.visit_symbol(s),
                SteelVal::Custom(c) => self.visit_custom_type(c),
                HashMapV(h) => self.visit_hash_map(h),
                HashSetV(s) => self.visit_hash_set(s),
                CustomStruct(c) => self.visit_steel_struct(c),
                PortV(p) => self.visit_port(p),
                IterV(t) => self.visit_transducer(t),
                ReducerV(r) => self.visit_reducer(r),
                FutureFunc(f) => self.visit_future_function(f),
                FutureV(f) => self.visit_future(f),
                StreamV(s) => self.visit_stream(s),
                BoxedFunction(b) => self.visit_boxed_function(b),
                ContinuationFunction(c) => self.visit_continuation(c),
                ListV(l) => self.visit_list(l),
                MutFunc(m) => self.visit_mutable_function(m),
                BuiltIn(b) => self.visit_builtin_function(b),
                MutableVector(b) => self.visit_mutable_vector(b),
                BoxedIterator(b) => self.visit_boxed_iterator(b),
                SteelVal::SyntaxObject(s) => self.visit_syntax_object(s),
                Boxed(b) => self.visit_boxed_value(b),
                Reference(r) => self.visit_reference_value(r),
                HeapAllocated(b) => self.visit_heap_allocated(b),
                Pair(p) => self.visit_pair(p),
                ByteVector(b) => self.visit_bytevector(b),
            };
        }
    }

    fn push_back(&mut self, value: SteelVal) {
        // TODO: Determine if all numbers should push back.
        match &value {
            SteelVal::BoxedFunction(function) => {
                if let Some(properties) = self.struct_types.function_properties(function) {
                    self.push_back(properties);
                }
                // Native functions and futures can run arbitrary code when dropped.
                self.released.push(value);
            }
            SteelVal::FutureFunc(_) | SteelVal::FutureV(_) => self.released.push(value),
            SteelVal::BoolV(_)
            | SteelVal::NumV(_)
            | SteelVal::IntV(_)
            | SteelVal::CharV(_)
            | SteelVal::Void
            | SteelVal::StringV(_)
            | SteelVal::FuncV(_)
            | SteelVal::SymbolV(_)
            | SteelVal::MutFunc(_)
            | SteelVal::BuiltIn(_)
            | SteelVal::ByteVector(_)
            | SteelVal::BigNum(_) => {}
            _ => {
                self.queue.push(value);
            }
        }
    }

    fn visit_bytevector(&mut self, _bytevector: crate::rvals::SteelByteVector) -> Self::Output {}
    fn visit_bignum(&mut self, _: Gc<BigInt>) -> Self::Output {}
    fn visit_complex(&mut self, _: Gc<SteelComplex>) -> Self::Output {}
    fn visit_bool(&mut self, _boolean: bool) -> Self::Output {}
    fn visit_boxed_function(&mut self, _function: Gc<BoxedDynFunction>) -> Self::Output {}
    // TODO: Revisit this when the boxed iterator is cleaned up
    fn visit_boxed_iterator(&mut self, iterator: GcMut<OpaqueIterator>) -> Self::Output {
        self.push_back(iterator.read().root.clone());
    }
    fn visit_boxed_value(&mut self, boxed_value: GcMut<SteelVal>) -> Self::Output {
        if self.visited.insert(boxed_value.as_ptr() as usize) {
            self.push_back(boxed_value.read().clone());
        }
    }

    fn visit_builtin_function(&mut self, _function: BuiltInSignature) -> Self::Output {}

    fn visit_char(&mut self, _c: char) -> Self::Output {}
    fn visit_closure(&mut self, closure: Gc<ByteCodeLambda>) -> Self::Output {
        // for heap_ref in closure.heap_allocated.borrow().iter() {
        // todo!()
        // self.mark_heap_reference(&heap_ref.strong_ptr())
        // }

        for capture in closure.captures() {
            self.push_back(capture.clone());
        }

        if let Some(contract) = closure.get_contract_information().as_ref() {
            self.push_back(contract.clone());
        }

        for instruction in closure.body_exp.iter() {
            match instruction.op_code {
                // If this instruction touches this global variable,
                // then we want to mark it as possibly referenced here.
                OpCode::CALLGLOBAL
                | OpCode::CALLPRIMITIVE
                | OpCode::PUSH
                | OpCode::CALLGLOBALTAIL
                | OpCode::CALLGLOBALNOARITY
                | OpCode::CALLGLOBALTAILNOARITY => {
                    let index = instruction.payload_size.to_usize();
                    if self
                        .rooted_functions
                        .is_none_or(|functions| functions.contains(&closure.id))
                        && self.slots.remove(&index)
                    {
                        self.kept.push(index);
                    }
                }
                _ => {}
            }
        }
    }
    fn visit_continuation(&mut self, continuation: Continuation) -> Self::Output {
        let continuation = (*continuation.inner.read()).clone();

        match continuation {
            ContinuationMark::Closed(continuation) => {
                for value in &continuation.stack {
                    self.push_back(value.clone());
                }

                for value in &continuation.current_frame.function.captures {
                    self.push_back(value.clone());
                }

                for frame in &continuation.stack_frames {
                    for value in &frame.function.captures {
                        self.push_back(value.clone());
                    }

                    // if let Some(handler) = &frame.handler {
                    //     self.push_back((*handler.as_ref()).clone());
                    // }

                    if let Some(handler) =
                        frame.attachments.as_ref().and_then(|x| x.handler.clone())
                    {
                        self.push_back(handler);
                    }
                }
            }

            ContinuationMark::Open(continuation) => {
                for value in &continuation.current_stack_values {
                    self.push_back(value.clone());
                }

                for value in &continuation.current_frame.function.captures {
                    self.push_back(value.clone());
                }
            }
        }
    }
    // TODO: Come back to this
    fn visit_custom_type(&mut self, custom_type: GcMut<Box<dyn CustomType>>) -> Self::Output {
        if !self.visited.insert(custom_type.as_ptr() as usize) {
            return;
        }

        let Some(custom) = read_custom_type(&custom_type) else {
            return;
        };
        let properties = self
            .struct_types
            .descriptor_properties(custom.as_ref());
        if let Some(properties) = properties {
            self.push_back(properties);
        }

        #[cfg(feature = "sync")]
        if custom.as_any_ref().is::<WillExecutor>() {
            self.will_executors.push(custom_type.clone());
        }

        let mut queue = MarkAndSweepContext {
            queue: &mut self.queue,
            stats: MarkAndSweepStats::default(),
            visited: core::mem::take(&mut self.visited),
            owned: None,
            trace_once: false,
            visited_lists: Default::default(),
            struct_types: core::mem::take(&mut self.struct_types),
        };

        custom.visit_children(&mut queue);
        self.visited = queue.visited;
        self.struct_types = queue.struct_types;
        self.released.append(&mut queue.stats.keep_alive);
    }

    fn visit_float(&mut self, _float: f64) -> Self::Output {}

    fn visit_function_pointer(&mut self, _ptr: FunctionSignature) -> Self::Output {}

    fn visit_future(&mut self, _future: Gc<FutureResult>) -> Self::Output {}

    fn visit_future_function(&mut self, _function: BoxedAsyncFunctionSignature) -> Self::Output {}

    fn visit_hash_map(&mut self, hashmap: SteelHashMap) -> Self::Output {
        if !self.visited.insert(hashmap.0.as_ptr() as usize) {
            return;
        }
        for (key, value) in hashmap.iter() {
            self.push_back(key.clone());
            self.push_back(value.clone());
        }
    }

    fn visit_hash_set(&mut self, hashset: SteelHashSet) -> Self::Output {
        for value in hashset.iter() {
            self.push_back(value.clone());
        }
    }

    fn visit_heap_allocated(&mut self, heap_ref: HeapRef<SteelVal>) -> Self::Output {
        if self.visited.insert(heap_ref.as_ptr_usize()) {
            if let Some(heap_ref) = heap_ref.inner.upgrade() {
                self.push_back(heap_ref.read().value.clone());
            }
        }
    }

    fn visit_immutable_vector(&mut self, vector: SteelVector) -> Self::Output {
        for value in vector.iter() {
            self.push_back(value.clone());
        }
    }
    fn visit_int(&mut self, _int: isize) -> Self::Output {}
    fn visit_rational(&mut self, _: Rational32) -> Self::Output {}
    fn visit_bigrational(&mut self, _: Gc<BigRational>) -> Self::Output {}

    fn visit_list(&mut self, list: List<SteelVal>) -> Self::Output {
        for value in list {
            self.push_back(value);
        }
    }

    fn visit_mutable_function(&mut self, _function: MutFunctionSignature) -> Self::Output {}

    fn visit_mutable_vector(&mut self, vector: HeapRef<Vec<SteelVal>>) -> Self::Output {
        if self.visited.insert(vector.as_ptr_usize()) {
            if let Some(vector) = vector.inner.upgrade() {
                for value in &vector.read().value {
                    self.push_back(value.clone());
                }
            }
        }
    }

    fn visit_port(&mut self, _port: SteelPort) -> Self::Output {}

    fn visit_reducer(&mut self, reducer: Gc<Reducer>) -> Self::Output {
        match reducer.as_ref().clone() {
            Reducer::ForEach(f) => self.push_back(f),
            Reducer::Generic(rf) => {
                self.push_back(rf.initial_value);
                self.push_back(rf.function);
            }
            _ => {}
        }
    }

    // TODO: Revisit this
    fn visit_reference_value(&mut self, _reference: Gc<OpaqueReference<'static>>) -> Self::Output {}

    fn visit_steel_struct(&mut self, steel_struct: Gc<UserDefinedStruct>) -> Self::Output {
        if let Some(properties) = self.struct_types.properties(steel_struct.type_descriptor) {
            self.push_back(properties);
        }
        for field in steel_struct.fields.iter() {
            self.push_back(field.clone());
        }
    }

    fn visit_stream(&mut self, stream: Gc<LazyStream>) -> Self::Output {
        self.push_back(stream.initial_value.clone());
        self.push_back(stream.stream_thunk.clone());
    }

    fn visit_string(&mut self, _string: SteelString) -> Self::Output {}

    fn visit_symbol(&mut self, _symbol: SteelString) -> Self::Output {}

    fn visit_syntax_object(&mut self, syntax_object: Gc<Syntax>) -> Self::Output {
        if let Some(raw) = syntax_object.raw.clone() {
            self.push_back(raw);
        }

        self.push_back(syntax_object.syntax.clone());
    }

    fn visit_transducer(&mut self, transducer: Gc<Transducer>) -> Self::Output {
        for transducer in transducer.ops.iter() {
            match transducer.clone() {
                crate::values::transducers::Transducers::Map(m) => self.push_back(m),
                crate::values::transducers::Transducers::Filter(v) => self.push_back(v),
                crate::values::transducers::Transducers::Take(t) => self.push_back(t),
                crate::values::transducers::Transducers::Drop(d) => self.push_back(d),
                crate::values::transducers::Transducers::FlatMap(fm) => self.push_back(fm),
                crate::values::transducers::Transducers::Flatten => {}
                crate::values::transducers::Transducers::Window(w) => self.push_back(w),
                crate::values::transducers::Transducers::TakeWhile(tw) => self.push_back(tw),
                crate::values::transducers::Transducers::DropWhile(dw) => self.push_back(dw),
                crate::values::transducers::Transducers::Extend(e) => self.push_back(e),
                crate::values::transducers::Transducers::Cycle => {}
                crate::values::transducers::Transducers::Enumerating => {}
                crate::values::transducers::Transducers::Zipping(z) => self.push_back(z),
                crate::values::transducers::Transducers::Interleaving(i) => self.push_back(i),
                crate::values::transducers::Transducers::MapPair(i) => self.push_back(i),
            }
        }
    }

    fn visit_void(&mut self) -> Self::Output {}

    fn visit_pair(&mut self, pair: Gc<super::lists::Pair>) -> Self::Output {
        self.push_back(pair.car());
        self.push_back(pair.cdr());
    }
}

const GC_THRESHOLD: usize = 256 * 1000;
const GC_GROW_FACTOR: usize = 2;
const RESET_LIMIT: usize = 9;

// TODO: Do these roots needs to be truly global?
// Replace this with a lazy static
thread_local! {
    static ROOTS: RefCell<Roots> = RefCell::new(Roots::default());
}

// stash roots in the global area
#[cfg(feature = "sync")]
static GLOBAL_ROOTS: Lazy<Mutex<Roots>> = Lazy::new(|| Mutex::new(Roots::default()));

// Snapshot the registry before traversing values that can reenter it.
fn persistent_roots_snapshot() -> Vec<SteelVal> {
    persistent_roots_for(None)
}

// With a heap, leaves out roots that retain other heaps' cells: they keep those cells only for
// their source heap, so another heap tracing them would keep its own retention alive.
fn persistent_roots_for(heap: Option<usize>) -> Vec<SteelVal> {
    fn collect(roots: &Roots, heap: Option<usize>) -> Vec<SteelVal> {
        roots
            .roots
            .iter()
            .filter(|(key, _)| {
                heap.is_none()
                    || roots
                        .retention
                        .get(key)
                        .is_none_or(|source| Some(*source) == heap)
            })
            .map(|(_, value)| value.clone())
            .collect()
    }

    #[cfg(feature = "sync")]
    let roots = collect(&GLOBAL_ROOTS.lock().unwrap(), heap);
    #[cfg(not(feature = "sync"))]
    let roots = ROOTS
        .try_with(|roots| collect(&roots.borrow(), heap))
        .unwrap_or_default();
    roots
}

// A struct type's properties are reachable only through its instances, its descriptor
// value, its constructor, predicate, and accessors, and values serialized from them.
#[derive(Default)]
pub(crate) struct ReachedStructTypes(rustc_hash::FxHashSet<StructTypeDescriptor>);

impl ReachedStructTypes {
    // Returns the property map the first time a traversal reaches the type.
    fn properties(&mut self, descriptor: StructTypeDescriptor) -> Option<SteelVal> {
        if !self.0.insert(descriptor) {
            return None;
        }
        VTable::properties(descriptor).map(|map| SteelVal::HashMapV(map.into()))
    }

    fn function_properties(&mut self, function: &Gc<BoxedDynFunction>) -> Option<SteelVal> {
        self.properties(struct_function_descriptor(function)?)
    }

    fn descriptor_properties(&mut self, custom_type: &dyn CustomType) -> Option<SteelVal> {
        self.properties(*custom_type.as_any_ref().downcast_ref()?)
    }

    fn clear(&mut self) {
        self.0.clear();
    }
}

#[derive(Default)]
pub struct Roots {
    generation: usize,
    offset: usize,
    roots: rustc_hash::FxHashMap<(usize, usize), SteelVal>,
    // Roots a heap holds to keep another heap's cells, by the address of that source heap.
    retention: rustc_hash::FxHashMap<(usize, usize), usize>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct RootToken {
    generation: usize,
    offset: usize,
}

impl Drop for RootToken {
    fn drop(&mut self) {
        // A root can be released by another thread-local's destructor after the table's.
        #[cfg(not(feature = "sync"))]
        let value = ROOTS.try_with(|x| x.borrow_mut().free(self)).ok().flatten();

        #[cfg(feature = "sync")]
        let value = GLOBAL_ROOTS.lock().unwrap().free(self);

        // Native values can own more roots, so drop them after releasing the registry.
        drop(value);
    }
}

#[derive(Debug)]
pub struct RootedSteelVal {
    value: SteelVal,
    token: RootToken,
}

impl RootedSteelVal {
    pub fn value(&self) -> &SteelVal {
        &self.value
    }
}

impl Roots {
    fn root(&mut self, value: SteelVal) -> RootToken {
        let generation = self.generation;
        let offset = self.offset;

        self.offset += 1;

        self.roots.insert((generation, offset), value);

        RootToken { generation, offset }
    }

    fn root_retained(&mut self, value: SteelVal, source: usize) -> RootToken {
        let token = self.root(value);
        self.retention
            .insert((token.generation, token.offset), source);
        token
    }

    fn free(&mut self, token: &RootToken) -> Option<SteelVal> {
        let key = (token.generation, token.offset);
        self.retention.remove(&key);
        self.roots.remove(&key)
    }

    fn increment_generation(&mut self) {
        self.generation += 1;
    }
}

impl SteelVal {
    pub fn mark_rooted(&self) -> RootToken {
        #[cfg(feature = "sync")]
        {
            GLOBAL_ROOTS.lock().unwrap().root(self.clone())
        }

        #[cfg(not(feature = "sync"))]
        {
            ROOTS.with(|x| x.borrow_mut().root(self.clone()))
        }
    }

    // If we're storing in an external struct that could escape
    // the runtime, we probably want to be marked as rooted
    pub fn as_rooted(&self) -> RootedSteelVal {
        let token = self.mark_rooted();

        RootedSteelVal {
            token,
            value: self.clone(),
        }
    }

    // A root that only the heap at `source` traces.
    fn as_retention_root(&self, source: usize) -> RootedSteelVal {
        #[cfg(feature = "sync")]
        let token = GLOBAL_ROOTS
            .lock()
            .unwrap()
            .root_retained(self.clone(), source);

        #[cfg(not(feature = "sync"))]
        let token = ROOTS.with(|x| x.borrow_mut().root_retained(self.clone(), source));

        RootedSteelVal {
            token,
            value: self.clone(),
        }
    }
}

type HeapValue = StandardSharedMut<HeapAllocated<SteelVal>>;
type HeapVector = StandardSharedMut<HeapAllocated<Vec<SteelVal>>>;

type HeapElement<T> = StandardSharedMut<HeapAllocated<T>>;

#[cfg(feature = "sync")]
pub struct WillExecutor {
    // Determining if these are reachable should be either:
    // * Value is a weak reference: then you use weak references
    // * value is contained within _other_ will executors, so the will executors need to have references to
    //   each other to check if ther value is contained within other ones.
    values: Mutex<Vec<Option<PendingWill>>>,

    // The incoming queue. We'll drain on this when the reified buffer of values
    // is empty since we need to scan the values to find the right one.
    incoming: Receiver<PendingWill>,

    sender: Sender<PendingWill>,
}

#[cfg(feature = "sync")]
struct PendingWill {
    pair: Pair,
    ready: bool,
    collection_domain: Option<std::sync::Weak<()>>,
}

fn traced_identity(value: &SteelVal) -> Option<usize> {
    match value {
        SteelVal::Closure(gc) => Some(gc.as_ptr() as usize),
        SteelVal::VectorV(vector) => Some(vector.0.as_ptr() as usize),
        SteelVal::Custom(gc) => Some(gc.as_ptr() as usize),
        SteelVal::HashMapV(map) => Some(map.0.as_ptr() as usize),
        SteelVal::HashSetV(set) => Some(set.0.as_ptr() as usize),
        SteelVal::CustomStruct(gc) => Some(gc.as_ptr() as usize),
        SteelVal::IterV(gc) => Some(gc.as_ptr() as usize),
        SteelVal::ReducerV(gc) => Some(gc.as_ptr() as usize),
        SteelVal::StreamV(gc) => Some(gc.as_ptr() as usize),
        SteelVal::ContinuationFunction(continuation) => {
            Some(StandardShared::as_ptr(&continuation.inner) as usize)
        }
        SteelVal::ListV(list) => Some(list.as_ptr_usize()),
        SteelVal::Pair(gc) => Some(gc.as_ptr() as usize),
        SteelVal::MutableVector(vector) => Some(vector.as_ptr_usize()),
        SteelVal::SyntaxObject(gc) => Some(gc.as_ptr() as usize),
        SteelVal::BoxedIterator(gc) => Some(gc.as_ptr() as usize),
        SteelVal::Boxed(gc) => Some(gc.as_ptr() as usize),
        SteelVal::HeapAllocated(heap_ref) => Some(heap_ref.as_ptr_usize()),
        _ => None,
    }
}

#[cfg(feature = "sync")]
impl PendingWill {
    fn is_unreachable(&self) -> bool {
        match self.pair.car_ref() {
            SteelVal::Closure(gc) => Gc::strong_count(gc) == 1,
            SteelVal::VectorV(steel_vector) => Gc::strong_count(&steel_vector.0) == 1,
            SteelVal::StringV(steel_string) => Gc::strong_count(&steel_string.0) == 1,
            SteelVal::SymbolV(steel_string) => Gc::strong_count(&steel_string.0) == 1,
            SteelVal::Custom(gc) => Gc::strong_count(gc) == 1,
            SteelVal::HashMapV(steel_hash_map) => Gc::strong_count(&steel_hash_map.0) == 1,
            SteelVal::HashSetV(steel_hash_set) => Gc::strong_count(&steel_hash_set.0) == 1,
            SteelVal::CustomStruct(gc) => Gc::strong_count(gc) == 1,
            SteelVal::PortV(steel_port) => Gc::strong_count(&steel_port.port) == 1,
            SteelVal::IterV(gc) => Gc::strong_count(gc) == 1,
            SteelVal::ReducerV(gc) => Gc::strong_count(gc) == 1,
            SteelVal::FutureV(gc) => Gc::strong_count(gc) == 1,
            SteelVal::StreamV(gc) => Gc::strong_count(gc) == 1,
            SteelVal::BoxedFunction(gc) => Gc::strong_count(gc) == 1,
            SteelVal::ContinuationFunction(continuation) => {
                StandardShared::strong_count(&continuation.inner) == 1
            }
            SteelVal::ListV(generic_list) => generic_list.strong_count() == 1,
            SteelVal::Pair(gc) => Gc::strong_count(gc) == 1,

            // In theory, if this is a weak value, this can be the thing to check
            // the values.
            SteelVal::MutableVector(heap_ref) => {
                heap_ref.inner.upgrade().is_none() || WeakShared::weak_count(&heap_ref.inner) == 1
            }
            SteelVal::BoxedIterator(gc) => Gc::strong_count(gc) == 1,
            SteelVal::SyntaxObject(gc) => Gc::strong_count(gc) == 1,
            SteelVal::Boxed(gc) => Gc::strong_count(gc) == 1,
            SteelVal::HeapAllocated(heap_ref) => {
                heap_ref.inner.upgrade().is_none() || WeakShared::weak_count(&heap_ref.inner) == 1
            }
            SteelVal::Reference(gc) => Gc::strong_count(gc) == 1,
            SteelVal::BigNum(gc) => Gc::strong_count(gc) == 1,
            SteelVal::BigRational(gc) => Gc::strong_count(gc) == 1,
            SteelVal::Complex(gc) => Gc::strong_count(gc) == 1,
            SteelVal::ByteVector(steel_byte_vector) => {
                Gc::strong_count(&steel_byte_vector.vec) == 1
            }
            _ => false,
        }
    }
}

#[cfg(not(feature = "sync"))]
pub struct WillExecutor {}

#[cfg(feature = "sync")]
impl WillExecutor {
    fn block_until_incoming(&self) {
        log::debug!(target: "will", "Blocking until something shows in the queue");
        if let Ok(next) = self.incoming.recv() {
            self.values.lock().unwrap().push(Some(next));
        }
    }

    // Returns the pair of values next to be used. Not the best data structure choice.
    fn find_next(&self) -> Option<Pair> {
        log::debug!(target: "will", "Finding the next value in the will executor list");
        // Proactively check if the value is ready to be received.
        // TODO: Merge the behavior below and above since we can just return this value
        // immediately without putting on to the queue.
        let top_guard = self.values.lock().unwrap();
        if top_guard.is_empty() && self.incoming.is_empty() {
            log::debug!(target: "will", "Initial values list is empty. Waiting on the queue.");
            drop(top_guard);

            // Block until the next thing is pushed on
            if let Ok(next) = self.incoming.recv() {
                log::debug!(target: "will", "Found a value off the queue, trying to lock the values.");

                self.values.lock().unwrap().push(Some(next));
            }
        } else {
            drop(top_guard);
        }

        log::debug!(target: "will", "Done optimistically checking off the queue. Locking the values.");

        let mut guard = self.values.lock().unwrap();

        // Drain the incoming, push them in to the values:

        while let Ok(incoming) = self.incoming.try_recv() {
            // TODO: Use a free list here instead? That way we can
            // re-use the space provided from earlier? Run some compaction
            // every one in a while?
            guard.push(Some(incoming));
        }

        log::debug!(target: "will", "Iterating over the values to drop");

        // TODO:
        // Periodically run a compaction on this
        for pair_slot in guard.iter_mut() {
            if let Some(value) = pair_slot {
                if value.ready || value.is_unreachable() {
                    return Some(pair_slot.take().unwrap().pair);
                }
            }
        }

        // Compact the values
        guard.retain(|x| x.is_some());

        None
    }

    pub fn register(&self, key: SteelVal, func: SteelVal) -> Result<(), SteelErr> {
        self.register_in_domain(key, func, None)
    }

    fn register_in_domain(
        &self,
        key: SteelVal,
        func: SteelVal,
        collection_domain: Option<std::sync::Weak<()>>,
    ) -> Result<(), SteelErr> {
        log::debug!(target: "will", "Registering: {}", key);
        if !func.is_function() {
            stop!(TypeMismatch => "will-register expects a function, found: {}", func)
        }

        self.sender
            .send(PendingWill {
                pair: Pair {
                    car: key,
                    cdr: func,
                },
                ready: false,
                collection_domain,
            })
            .unwrap();

        Ok(())
    }
}

impl Custom for WillExecutor {
    #[cfg(feature = "sync")]
    fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
        let mut values = self.values.lock().unwrap();
        values.extend(self.incoming.try_iter().map(Some));
        for pending in values.iter().flatten() {
            context.push_back(pending.pair.car());
            context.push_back(pending.pair.cdr());
        }
    }

    fn into_serializable_steelval(&mut self) -> Option<crate::rvals::SerializableSteelVal> {
        Some(crate::rvals::SerializableSteelVal::Void)
    }
}

#[cfg(feature = "sync")]
#[steel_derive::function(name = "make-will-executor")]
pub fn make_will_executor() -> Result<SteelVal, SteelErr> {
    let (sender, incoming) = crossbeam_channel::unbounded();
    WillExecutor {
        values: Mutex::new(Vec::new()),
        sender,
        incoming,
    }
    .into_steelval()
}

#[cfg(not(feature = "sync"))]
#[steel_derive::function(name = "make-will-executor")]
pub fn make_will_executor() -> Result<SteelVal, SteelErr> {
    WillExecutor {}.into_steelval()
}

#[cfg(feature = "sync")]
#[steel_derive::context(name = "will-execute", arity = "Exact(1)")]
pub fn will_execute(ctx: &mut VmCore, args: &[SteelVal]) -> Option<Result<SteelVal, SteelErr>> {
    let executor = WillExecutor::as_ref(&args[0]).unwrap();

    // TODO: Make this find the next thing? Perhaps just have this be a channel
    // or something that waits until the next thing is found?
    // How to do this _with_ blocking? Maybe have a queue for values that are being registered,
    // and then otherwise drain the vector and put them in when found.
    if let SteelVal::Pair(pair) = ctx
        .thread
        .enter_safepoint(|_| -> Result<SteelVal, SteelErr> {
            loop {
                if let Some(value) = executor.find_next() {
                    return Ok(SteelVal::Pair(Gc::new(value)));
                } else {
                    // Control frequency here, but for when there is no throughput,
                    // we want to at least poll a bit
                    executor.block_until_incoming();
                }
            }
        })
        .unwrap()
    {
        let mut pair = pair.try_unwrap().unwrap();
        let car = core::mem::replace(&mut pair.car, SteelVal::Void);
        let cdr = core::mem::replace(&mut pair.cdr, SteelVal::Void);
        apply(ctx, &[cdr, SteelVal::ListV(vec![car].into())])
    } else {
        unreachable!()
    }
}

#[cfg(not(feature = "sync"))]
#[steel_derive::context(name = "will-execute", arity = "Exact(1)")]
pub fn will_execute(_ctx: &mut VmCore, args: &[SteelVal]) -> Option<Result<SteelVal, SteelErr>> {
    let _ = WillExecutor::as_ref(&args[0]).unwrap();
    Some(Ok(SteelVal::Void))
}

#[cfg(feature = "sync")]
#[steel_derive::context(name = "will-register", arity = "Exact(3)")]
pub fn will_register_in_context(
    ctx: &mut VmCore,
    args: &[SteelVal],
) -> Option<Result<SteelVal, SteelErr>> {
    Some((|| {
        let will = WillExecutor::as_ref(&args[0])?;
        // The arguments have left the VM stack, so this must not wait at a safepoint, where
        // another thread's collection would not see them, before they are registered.
        let domain = ctx.thread.heap.collection_domain();
        will.register_in_domain(args[1].clone(), args[2].clone(), Some(domain))?;
        Ok(SteelVal::Void)
    })())
}

#[cfg(feature = "sync")]
pub use WILL_REGISTER_IN_CONTEXT_DEFINITION as WILL_REGISTER_DEFINITION;

#[cfg(feature = "sync")]
pub fn will_register(
    will: SteelVal,
    value: SteelVal,
    func: SteelVal,
) -> Result<SteelVal, SteelErr> {
    WillExecutor::as_ref(&will)?.register(value, func)?;
    Ok(SteelVal::Void)
}

#[cfg(not(feature = "sync"))]
#[steel_derive::function(name = "will-register")]
pub fn will_register(
    _will: SteelVal,
    _value: SteelVal,
    _func: SteelVal,
) -> Result<SteelVal, SteelErr> {
    Ok(SteelVal::Void)
}

#[cfg(all(test, feature = "sync"))]
mod will_tests {
    use super::*;
    use crate::steel_vm::engine::Engine;

    fn engine_with_gc() -> Engine {
        let mut engine = Engine::new();
        let mut primitives = Engine::new_raw_no_kernel();
        crate::steel_vm::primitives::register_builtin_modules(&mut primitives, true);
        let meta = primitives.builtin_modules().get("steel/meta").unwrap();
        engine.register_value("probe-gc", meta.inner_map()["#%gc-collect"].clone());
        engine
    }

    fn readiness(engine: &Engine, name: &str) -> Vec<bool> {
        let value = engine.extract_value(name).unwrap();
        let executor = WillExecutor::as_ref(&value).unwrap();
        let values = executor.values.lock().unwrap();
        values
            .iter()
            .flatten()
            .map(|pending| pending.ready)
            .collect()
    }

    #[test]
    fn shared_executors_wait_for_the_keys_own_collection() {
        for key in ["(box 42)", "(vector 42)", "(list (box 42))"] {
            let mut owner = engine_with_gc();
            let mut foreign = engine_with_gc();
            owner.register_value(
                "probe-finalizer",
                SteelVal::FuncV(|_| Ok(SteelVal::IntV(42))),
            );
            owner
                .run(format!(
                    "(define executor (make-will-executor))
                     (define live {key})
                     (will-register executor live probe-finalizer)"
                ))
                .unwrap();
            foreign.register_value("executor", owner.extract_value("executor").unwrap());
            foreign.run("(probe-gc) (probe-gc)").unwrap();
            assert_eq!(readiness(&owner, "executor"), [false]);
            let executor = owner.extract_value("executor").unwrap();
            assert!(WillExecutor::as_ref(&executor)
                .unwrap()
                .find_next()
                .is_none());
            owner.run("(probe-gc)").unwrap();
            assert_eq!(readiness(&owner, "executor"), [false]);
            owner.run("(set! live #f)").unwrap();
            foreign.run("(probe-gc)").unwrap();
            owner.run("(probe-gc)").unwrap();
            assert_eq!(readiness(&owner, "executor"), [true]);
            assert_eq!(
                foreign.run("(will-execute executor)").unwrap(),
                [SteelVal::IntV(42)]
            );
            assert!(readiness(&owner, "executor").is_empty());
        }
    }

    #[test]
    fn retained_executors_do_not_root_their_pending_keys() {
        let mut owner = engine_with_gc();
        owner.register_value(
            "probe-finalizer",
            SteelVal::FuncV(|args| Ok(args[0].as_box_to_inner().unwrap())),
        );
        owner
            .run(
                "(define executor (make-will-executor))
                 (define key (box 42))
                 (will-register executor key probe-finalizer)",
            )
            .unwrap();
        let mut copy = owner.deep_clone();
        copy.register_value("alias", owner.extract_value("key").unwrap());
        copy.run("(probe-gc)").unwrap();
        owner.run("(set! key #f)").unwrap();
        owner.run("(probe-gc)").unwrap();
        assert_eq!(readiness(&owner, "executor"), [false]);
        copy.run("(set! alias #f)").unwrap();
        copy.run("(probe-gc)").unwrap();
        owner.run("(probe-gc)").unwrap();
        assert_eq!(readiness(&owner, "executor"), [true]);
        drop(owner);
        copy.run("(probe-gc)").unwrap();
        assert_eq!(
            copy.run("(will-execute executor)").unwrap(),
            [SteelVal::IntV(42)]
        );
    }

    #[test]
    fn constant_lists_remain_ordinary_will_roots() {
        let mut engine = engine_with_gc();
        engine
            .run(
                "(define executor (make-will-executor))
                 (define (live) '(1 2 3 4))
                 (will-register executor (live) (lambda (value) 42))",
            )
            .unwrap();
        for _ in 0..3 {
            engine.run("(probe-gc)").unwrap();
            assert_eq!(readiness(&engine, "executor"), [false]);
        }
        assert_eq!(engine.run("(live)").unwrap()[0].to_string(), "(1 2 3 4)");
    }

    #[test]
    fn struct_properties_follow_type_reachability() {
        let mut engine = engine_with_gc();
        engine
            .run(
                "(define executor (make-will-executor))
                 (define owner
                   (let ((key (list (box 1) 2 3 4)))
                     (will-register executor key (lambda (value) 42))
                     (struct holder () #:key key)
                     (holder)))",
            )
            .unwrap();
        for _ in 0..3 {
            engine.run("(probe-gc)").unwrap();
            assert_eq!(readiness(&engine, "executor"), [false]);
            assert_eq!(
                engine
                    .run("(unbox (car (#%struct-property-ref owner '#:key)))")
                    .unwrap(),
                [SteelVal::IntV(1)]
            );
        }
        engine.run("(set! owner #f)").unwrap();
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(readiness(&engine, "executor"), [true]);
        assert_eq!(
            engine.run("(will-execute executor)").unwrap(),
            [SteelVal::IntV(42)]
        );
    }

    #[test]
    fn forked_thread_constants_remain_ordinary_will_roots() {
        use crate::steel_vm::vm::{StackFrame, SteelThread};
        use std::sync::Arc;

        struct Fork(#[allow(dead_code)] Arc<Mutex<SteelThread>>);
        impl Custom for Fork {}

        fn retain_in_fork(
            ctx: &mut VmCore,
            args: &[SteelVal],
        ) -> Option<Result<SteelVal, SteelErr>> {
            let fork = ctx.make_thread();
            {
                let mut thread = fork.lock().unwrap();
                thread.stack.clear();
                thread.stack_frames.clear();
                thread.current_frame = StackFrame::main();
                thread.constant_map = ConstantMap::from_vec(vec![args[0].clone()]);
            }
            Some(Fork(fork).into_steelval())
        }

        let mut engine = engine_with_gc();
        engine.register_value("probe-fork", SteelVal::BuiltIn(retain_in_fork));
        engine
            .run(
                "(define executor (make-will-executor))
                 (define owner
                   (let ((key (list (box 1) 2 3 4)))
                     (will-register executor key (lambda (value) 42))
                     (probe-fork key)))",
            )
            .unwrap();
        for _ in 0..3 {
            engine.run("(probe-gc)").unwrap();
            assert_eq!(readiness(&engine, "executor"), [false]);
        }
        engine.run("(set! owner #f)").unwrap();
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(readiness(&engine, "executor"), [true]);
    }

    #[test]
    fn shared_list_tails_remain_ordinary_will_roots() {
        let mut engine = engine_with_gc();
        engine
            .run(
                "(define executor (make-will-executor))
                 (define owner
                   (let ((key (list (box 1) 2 3 4)))
                     (will-register executor key (lambda (value) 42))
                     (cons 0 key)))",
            )
            .unwrap();
        for _ in 0..3 {
            engine.run("(probe-gc)").unwrap();
            assert_eq!(readiness(&engine, "executor"), [false]);
        }
        engine.run("(set! owner #f)").unwrap();
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert_eq!(readiness(&engine, "executor"), [true]);
        assert_eq!(
            engine.run("(will-execute executor)").unwrap(),
            [SteelVal::IntV(42)]
        );
    }

    #[test]
    fn untraced_will_keys_keep_reference_count_eligibility() {
        let mut engine = engine_with_gc();
        engine
            .run("(define executor (make-will-executor))")
            .unwrap();
        let executor_value = engine.extract_value("executor").unwrap();
        let executor = WillExecutor::as_ref(&executor_value).unwrap();
        let key = SteelVal::StringV("native key".into());
        executor
            .register(key.clone(), SteelVal::FuncV(|args| Ok(args[0].clone())))
            .unwrap();
        engine.run("(probe-gc)").unwrap();
        assert_eq!(readiness(&engine, "executor"), [false]);
        drop(key);
        engine.run("(probe-gc)").unwrap();
        assert_eq!(readiness(&engine, "executor"), [true]);
        assert_eq!(
            engine.run("(will-execute executor)").unwrap(),
            [SteelVal::StringV("native key".into())]
        );
    }

    #[test]
    fn executing_closures_remain_ordinary_will_roots() {
        use crate::steel_vm::register_fn::RegisterFn;

        let mut engine = engine_with_gc();
        engine.register_fn("will-ready?", |value: SteelVal| {
            WillExecutor::as_ref(&value)
                .unwrap()
                .values
                .lock()
                .unwrap()
                .iter()
                .flatten()
                .any(|pending| pending.ready)
        });
        engine
            .run(
                r#"
                (define executor (make-will-executor))
                (define live
                  (lambda ()
                    (set! live #f)
                    (probe-gc)
                    (will-ready? executor)))
                (will-register executor live (lambda (value) 42))
                "#,
            )
            .unwrap();
        assert_eq!(engine.run("(live)").unwrap(), [SteelVal::BoolV(false)]);
        engine.run("(probe-gc)").unwrap();
        assert_eq!(readiness(&engine, "executor"), [true]);
    }

    #[test]
    fn cyclic_will_keys_follow_ordinary_reachability() {
        let mut engine = engine_with_gc();
        engine
            .run(
                r#"
                (define executor (make-will-executor))
                (define calls 0)
                (define live
                  (let ((items (vector #f 42)))
                    (define key (list items))
                    (vector-set! items 0 key)
                    key))
                (will-register executor live
                  (lambda (value)
                    (probe-gc)
                    (set! calls (+ calls 1))
                    (vector-ref (car value) 1)))
                (probe-gc) (probe-gc) (probe-gc)
                "#,
            )
            .unwrap();
        assert_eq!(readiness(&engine, "executor"), [false]);
        engine
            .run("(set! live #f) (probe-gc) (probe-gc) (probe-gc)")
            .unwrap();
        // set! returns the cycle, so this execution still retained an ordinary root.
        assert_eq!(readiness(&engine, "executor"), [false]);
        engine.run("(probe-gc) (probe-gc)").unwrap();
        // Check readiness before calling the blocking will-execute primitive.
        assert_eq!(readiness(&engine, "executor"), [true]);
        assert_eq!(
            engine.run("(will-execute executor)").unwrap(),
            [SteelVal::IntV(42)]
        );
        engine.run("(probe-gc) (probe-gc)").unwrap();
        assert!(readiness(&engine, "executor").is_empty());
        assert_eq!(engine.run("calls").unwrap(), [SteelVal::IntV(1)]);
    }

    #[test]
    fn executors_discovered_during_retention_use_ordinary_reachability() {
        let mut engine = engine_with_gc();
        engine
            .run(
                r#"
                (define outer (make-will-executor))
                (let ((inner (make-will-executor)) (key (box 42)))
                  (will-register inner key unbox)
                  (will-register outer key (lambda (value) inner)))
                (probe-gc) (probe-gc)
                "#,
            )
            .unwrap();
        assert_eq!(readiness(&engine, "outer"), [true]);
        engine.run("(define inner (will-execute outer))").unwrap();
        assert_eq!(readiness(&engine, "inner"), [true]);
        assert_eq!(
            engine.run("(will-execute inner)").unwrap(),
            [SteelVal::IntV(42)]
        );
    }
}

// Not considered part of the reachability graph? i.e. we simply don't traverse it.
pub struct WeakBox {
    value: HeapRef<SteelVal>,
}

impl Custom for WeakBox {}

/// Allocates a weak box.
///
/// A weak box is similar to a box, but when the garbage collector can prove
/// that the value of a weak box is only reachable through weak references,
/// the weak box value will always return #false.
///
/// In other words, a weak box does not keep the value contained alive through
/// a gc collection.
#[steel_derive::context(name = "make-weak-box", arity = "Exact(1)")]
pub fn make_weak_box(ctx: &mut VmCore, args: &[SteelVal]) -> Option<Result<SteelVal, SteelErr>> {
    let value = args[0].clone();
    if let SteelVal::HeapAllocated(made_box) = ctx.make_box(value) {
        Some(WeakBox { value: made_box }.into_steelval())
    } else {
        unreachable!()
    }
}

/// Returns the value contained in the weak box.
/// If the garbage collector has proven that the previous content
/// value of weak-box was reachable only through a weak reference,
/// then default-value (which defaults to #f) is returned.
///
/// ```scheme
/// (define value (make-weak-box 10))
/// (weak-box-value value) ;; => 10
/// (set! value #f) ;; Wipe out the previous value
/// (#%gc-collect)
/// (weak-box-value value) ;; => #false
/// ```
#[steel_derive::function(name = "weak-box-value")]
pub fn weak_box_value(
    value: &SteelVal,
    mut rest: RestArgsIter<&SteelVal>,
) -> Result<SteelVal, SteelErr> {
    let inner = WeakBox::as_ref(value)?;

    // Check if its reachable?
    if let Some(value) = inner.value.maybe_get_from_weak() {
        Ok(value)
    } else {
        Ok(rest
            .next()
            .map(|x| x.unwrap().clone())
            .unwrap_or(SteelVal::BoolV(false)))
    }
}

// Have free list for vectors and values separately. Can keep some of the vectors pre allocated
// as well, as necessary.
//
// Also -> implement will / executor functionality for implementing destructors for objects.
// This should be _relatively_ straightforward. When allocating a value, send it on the destructor
// thread.
#[derive(Debug)]
struct FreeList<T: HeapAble> {
    // TODO: Make this a linked list of vectors. Can reuse im-lists?
    // Pointer chasing may not be worth it. The issue is every doubling of size _also_
    // allocate a whole bunch more. Can probably just get away with a vec of vecs to avoid
    // copying everything.
    elements: Vec<HeapElement<T>>,
    cursor: usize,

    // Available count
    alloc_count: usize,

    grow_count: usize,

    #[cfg(feature = "sync")]
    forward: Option<Sender<Vec<HeapElement<T>>>>,
    #[cfg(feature = "sync")]
    backward: Option<Receiver<Vec<HeapElement<T>>>>,

    should_run_weak: bool,
}

impl<T: HeapAble> Clone for FreeList<T> {
    fn clone(&self) -> Self {
        Self {
            cursor: self.cursor,
            alloc_count: self.alloc_count,
            grow_count: self.grow_count,
            elements: self
                .elements
                .iter()
                .map(|x| {
                    let guard = x.read();
                    let inner = guard.value.clone();
                    StandardShared::new(MutContainer::new(HeapAllocated {
                        reachable: guard.reachable,
                        finalizer: guard.finalizer,
                        value: inner,
                    }))
                })
                .collect(),
            #[cfg(feature = "sync")]
            forward: None,
            #[cfg(feature = "sync")]
            backward: None,

            should_run_weak: self.should_run_weak,
        }
    }
}

#[test]
fn basic_free_list_usage() {
    // Pre allocate some slots
    let mut free_list: FreeList<SteelVal> = FreeList::new();

    let pointers = (0..100)
        .into_iter()
        .map(|x| free_list.allocate(SteelVal::IntV(x)))
        .collect::<Vec<_>>();

    drop(pointers);

    free_list.weak_collection(drop);

    for var in &free_list.elements {
        assert!(!var.read().is_reachable());
    }
}

#[cfg(test)]
fn mark_test_roots(heap: &Heap, roots: &[SteelVal], _borrowed: bool) -> MarkAndSweepStats {
    let owned = heap.cell_addresses();
    #[cfg(feature = "sync")]
    if _borrowed {
        let queue = crossbeam_queue::SegQueue::new();
        let mut local_queue = Vec::new();
        let mut marker = MarkAndSweepContextRefQueue {
            collection_domain: None,
            queue: &queue,
            local_queue: &mut local_queue,
            stats: MarkAndSweepStats::default(),
            visited: Default::default(),
            will_executors: Vec::new(),
            reachable: Default::default(),
            owned: &owned,
            struct_types: Default::default(),
        };
        for root in roots {
            marker.push_back(root);
        }
        marker.visit();
        return marker.stats;
    }
    let mut queue = Vec::new();
    let mut marker = MarkAndSweepContext {
        queue: &mut queue,
        stats: MarkAndSweepStats::default(),
        visited: Default::default(),
        owned: Some(&owned),
        trace_once: false,
        visited_lists: Default::default(),
        struct_types: Default::default(),
    };
    for root in roots {
        marker.push_back(root.clone());
    }
    marker.visit();
    marker.stats
}

#[test]
fn marking_isolates_foreign_cells_and_reaches_local_descendants() {
    for borrowed in [false, cfg!(feature = "sync")] {
        for custom in [false, true] {
            let mut local = Heap::new();
            let mut foreign = Heap::new();
            let child = local.allocate_without_collection(SteelVal::IntV(42));
            let local_vector = local.allocate_vec_without_collection(vec![]);
            let parent =
                foreign.allocate_without_collection(SteelVal::MutableVector(local_vector.clone()));
            let parent_vector = foreign
                .allocate_vec_without_collection(vec![SteelVal::HeapAllocated(parent.clone())]);
            local_vector.set_interior_mut(vec![
                SteelVal::HeapAllocated(child.clone()),
                SteelVal::MutableVector(parent_vector.clone()),
            ]);
            let root = if custom {
                DirectHeapChildren {
                    value: parent.clone(),
                    vector: parent_vector.clone(),
                }
                .into_steelval()
                .unwrap()
            } else {
                SteelVal::MutableVector(parent_vector.clone())
            };
            for marked in [false, true] {
                parent.strong_ptr().write().reachable = marked;
                parent_vector.strong_ptr().write().reachable = marked;
                local.memory_free_list.mark_all_unreachable();
                local.vector_free_list.mark_all_unreachable();
                let stats = mark_test_roots(&local, std::slice::from_ref(&root), borrowed);
                assert!(child.strong_ptr().read().reachable);
                assert!(local_vector.strong_ptr().read().reachable);
                assert_eq!(parent.strong_ptr().read().reachable, marked);
                assert_eq!(parent_vector.strong_ptr().read().reachable, marked);
                assert_eq!(stats.memory_reached_count, 1);
                assert_eq!(stats.vector_reached_count, 1);
            }
        }
    }
}

#[cfg(feature = "sync")]
#[test]
fn concurrent_collectors_do_not_share_foreign_marks() {
    use std::time::Duration;

    let mut first = Heap::new();
    let mut second = Heap::new();
    let second_child = second.allocate_without_collection(SteelVal::IntV(42));
    let first_child =
        first.allocate_without_collection(SteelVal::HeapAllocated(second_child.clone()));
    let parent =
        first.allocate_vec_without_collection(vec![SteelVal::HeapAllocated(first_child.clone())]);
    first.memory_free_list.mark_all_unreachable();
    first.vector_free_list.mark_all_unreachable();
    second.memory_free_list.mark_all_unreachable();
    let (ready_tx, ready_rx) = crossbeam_channel::bounded(1);
    let (resume_tx, resume_rx) = crossbeam_channel::bounded(1);
    let foreign_parent = parent.clone();
    let worker = std::thread::spawn(move || {
        let owned = second.cell_addresses();
        let queue = crossbeam_queue::SegQueue::new();
        let mut local_queue = Vec::new();
        let mut marker = MarkAndSweepContextRefQueue {
            collection_domain: None,
            queue: &queue,
            local_queue: &mut local_queue,
            stats: MarkAndSweepStats::default(),
            visited: Default::default(),
            will_executors: Vec::new(),
            reachable: Default::default(),
            owned: &owned,
            struct_types: Default::default(),
        };
        marker.visit_mutable_vector(foreign_parent);
        ready_tx.send(()).unwrap();
        resume_rx.recv_timeout(Duration::from_secs(10)).unwrap();
        marker.visit();
        assert!(second_child.strong_ptr().read().reachable);
        assert_eq!(marker.stats.memory_reached_count, 1);
        assert_eq!(marker.stats.vector_reached_count, 0);
    });
    ready_rx.recv_timeout(Duration::from_secs(10)).unwrap();
    // The second collector has queued the first heap's child but has not visited it.
    let stats = mark_test_roots(&first, &[SteelVal::MutableVector(parent)], true);
    resume_tx.send(()).unwrap();
    worker.join().unwrap();
    assert!(first_child.strong_ptr().read().reachable);
    assert_eq!(stats.memory_reached_count, 1);
    assert_eq!(stats.vector_reached_count, 1);
}

#[cfg(feature = "sync")]
#[test]
fn local_heap_traversal_does_not_retain_each_vector_element() {
    let mut heap = Heap::new();
    let child = heap.allocate_without_collection(SteelVal::IntV(42));
    let root = SteelVal::MutableVector(
        heap.allocate_vec_without_collection(
            (0..10_000)
                .map(|_| SteelVal::HeapAllocated(child.clone()))
                .collect(),
        ),
    );
    heap.memory_free_list.mark_all_unreachable();
    heap.vector_free_list.mark_all_unreachable();
    let stats = mark_test_roots(&heap, &[root], true);
    assert_eq!(stats.memory_reached_count, 1);
    assert_eq!(stats.vector_reached_count, 1);
    assert!(stats.keep_alive.is_empty());
}

#[test]
fn teardown_traces_descendants_without_changing_foreign_marks() {
    let mut foreign = Heap::new();
    let child = foreign.allocate_without_collection(SteelVal::IntV(42));
    let parent =
        foreign.allocate_vec_without_collection(vec![SteelVal::HeapAllocated(child.clone())]);
    for marked in [true, false] {
        child.strong_ptr().write().reachable = marked;
        parent.strong_ptr().write().reachable = marked;
        // Keep this root private so parallel tests' normal collectors cannot mark it.
        let mut queue = Vec::new();
        let mut context = MarkAndSweepContext {
            queue: &mut queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            owned: None,
            trace_once: true,
            visited_lists: Default::default(),
            struct_types: Default::default(),
        };
        context.push_back(SteelVal::MutableVector(parent.clone()));
        context.visit();
        assert!(context.visited.contains(&child.as_ptr_usize()));
        assert!(context.visited.contains(&parent.as_ptr_usize()));
        assert_eq!(child.strong_ptr().read().reachable, marked);
        assert_eq!(parent.strong_ptr().read().reachable, marked);
    }
}

#[test]
fn teardown_retains_registered_descendants_and_detaches_only_local_payloads() {
    let mut heap = Heap::new();
    let child = heap.allocate_without_collection(SteelVal::IntV(42));
    let root = SteelVal::MutableVector(
        heap.allocate_vec_without_collection(vec![SteelVal::HeapAllocated(child.clone())]),
    )
    .as_rooted();
    let unreachable = heap.allocate_without_collection(SteelVal::IntV(99));
    let (reachable, keep_alive) = Heap::trace_teardown_roots();
    drop(heap.detach_unreachable(&reachable));
    assert_eq!(child.get(), SteelVal::IntV(42));
    assert_eq!(unreachable.get(), SteelVal::Void);
    drop(keep_alive);
    drop(root);
    let (reachable, keep_alive) = Heap::trace_teardown_roots();
    drop(heap.detach_unreachable(&reachable));
    assert_eq!(child.get(), SteelVal::Void);
    drop(keep_alive);
}

#[test]
fn free_list_continues_allocating_when_full() {
    // Pre allocate some slots
    let mut free_list: FreeList<SteelVal> = FreeList::new();

    let count: usize = 10000;

    let pointers = (0..count)
        .into_iter()
        .map(|x| free_list.allocate(SteelVal::IntV(x as isize)))
        .collect::<Vec<_>>();

    for var in &free_list.elements[0..count] {
        assert!(var.read().is_reachable());
    }

    for var in &free_list.elements[count..] {
        assert!(!var.read().is_reachable());
    }

    drop(pointers);

    free_list.weak_collection(drop);

    for var in &free_list.elements {
        assert!(!var.read().is_reachable());
    }
}

#[test]
fn free_list_continues_allocating_in_the_middle() {
    // Pre allocate some slots
    let mut free_list: FreeList<SteelVal> = FreeList::new();

    let count: usize = 10000;

    let mut pointers = (0..count)
        .into_iter()
        .map(|x| free_list.allocate(SteelVal::IntV(x as isize)))
        .collect::<Vec<_>>();

    for var in &free_list.elements[0..count] {
        assert!(var.read().is_reachable());
    }

    for var in &free_list.elements[count..] {
        assert!(!var.read().is_reachable());
    }

    let right_half = pointers.split_off(100);

    drop(pointers);

    free_list.weak_collection(drop);

    // Check that the first 100 elements are in fact, gone

    for var in &free_list.elements[0..100] {
        assert!(!var.read().is_reachable());
    }

    drop(right_half)
}

#[cfg(feature = "sync")]
#[test]
fn borrowed_heap_traversal_keeps_children_after_heap_teardown() {
    use std::sync::Arc;

    struct Probe(Arc<()>, HeapRef<SteelVal>);
    impl Custom for Probe {
        fn gc_visit_children(&self, context: &mut MarkAndSweepContext) {
            context.push_back(SteelVal::HeapAllocated(self.1.clone()));
        }
    }

    for vector in [false, true] {
        for marked in [false, true] {
            for teardown in [false, true] {
                let count = Arc::new(());
                let mut local = Heap::new();
                let descendant = local.allocate_without_collection(SteelVal::IntV(42));
                local.memory_free_list.mark_all_unreachable();
                let mut foreign = Heap::new();
                let child = Probe(count.clone(), descendant.clone())
                    .into_steelval()
                    .unwrap();
                let root = if vector {
                    let cell = foreign.allocate_vec_without_collection(vec![child]);
                    cell.strong_ptr().write().reachable = marked;
                    SteelVal::MutableVector(cell)
                } else {
                    let cell = foreign.allocate_without_collection(child);
                    cell.strong_ptr().write().reachable = marked;
                    SteelVal::HeapAllocated(cell)
                };
                let owned = local.cell_addresses();
                let queue = crossbeam_queue::SegQueue::new();
                let mut local_queue = Vec::new();
                let mut marker = MarkAndSweepContextRefQueue {
                    collection_domain: None,
                    queue: &queue,
                    local_queue: &mut local_queue,
                    stats: MarkAndSweepStats::default(),
                    visited: rustc_hash::FxHashSet::default(),
                    will_executors: Vec::new(),
                    reachable: rustc_hash::FxHashSet::default(),
                    owned: &owned,
                    struct_types: Default::default(),
                };
                match &root {
                    SteelVal::HeapAllocated(value) => marker.visit_heap_allocated(value.clone()),
                    SteelVal::MutableVector(value) => marker.visit_mutable_vector(value.clone()),
                    _ => unreachable!(),
                }
                let foreign_root = root.clone();
                std::thread::spawn(move || {
                    if teardown {
                        drop(foreign);
                    } else {
                        match foreign_root {
                            SteelVal::HeapAllocated(value) => {
                                value.set_interior_mut(SteelVal::Void);
                            }
                            SteelVal::MutableVector(value) => {
                                value.set_interior_mut(vec![]);
                            }
                            _ => unreachable!(),
                        }
                    }
                })
                .join()
                .unwrap();
                #[cfg(feature = "biased")]
                steel_rc::QueueHandle::run_explicit_merge();
                assert_eq!(Arc::strong_count(&count), 2);
                // The queued child must outlive replacement or teardown of its foreign cell.
                marker.push_back(&root);
                marker.visit();
                assert!(descendant.strong_ptr().read().reachable);
                assert_eq!(marker.stats.memory_reached_count, 1);
                assert_eq!(marker.stats.vector_reached_count, 0);
                drop(marker);
                assert_eq!(Arc::strong_count(&count), 1);
            }
        }
    }
}

#[cfg(feature = "sync")]
#[test]
fn parallel_mark_counts_each_slot_exactly_once() {
    use std::sync::{Arc, Barrier};

    let num_slots = 4000;
    let num_threads = 8;

    let slots: Arc<Vec<HeapElement<SteelVal>>> = Arc::new(
        (0..num_slots)
            .map(|_| StandardShared::new(MutContainer::new(HeapAllocated::new(SteelVal::Void))))
            .collect(),
    );

    let barrier = Arc::new(Barrier::new(num_threads));

    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let slots = Arc::clone(&slots);
            let barrier = Arc::clone(&barrier);
            std::thread::spawn(move || {
                let owned = slots
                    .iter()
                    .map(|slot| StandardShared::as_ptr(slot) as usize)
                    .collect();
                let queue = crossbeam_queue::SegQueue::new();
                let mut local_queue = Vec::new();
                let mut ctx = MarkAndSweepContextRefQueue {
                    collection_domain: None,
                    local_queue: &mut local_queue,
                    queue: &queue,
                    stats: MarkAndSweepStats::default(),
                    visited: rustc_hash::FxHashSet::default(),
                    will_executors: Vec::new(),
                    reachable: rustc_hash::FxHashSet::default(),
                    owned: &owned,
                    struct_types: Default::default(),
                };

                barrier.wait();
                for slot in slots.iter() {
                    ctx.mark_heap_reference(slot);
                }

                ctx.stats.memory_reached_count
            })
        })
        .collect();

    let total: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();

    assert_eq!(total, num_slots);
    for slot in slots.iter() {
        assert!(slot.read().is_reachable());
    }
}

#[cfg(feature = "sync")]
impl<T: HeapAble + Sync + Send + 'static> FreeList<T> {
    // TODO: Calculate the overhead!
    // How big is this?
    const EXTEND_CHUNK: usize = 256;

    fn new() -> Self {
        // #[cfg(feature = "sync")]
        // let (forward_sender, backward_receiver) = spawn_background_dropper();

        let mut res = FreeList {
            elements: Vec::new(),
            cursor: 0,
            alloc_count: 0,
            grow_count: 0,
            // #[cfg(feature = "sync")]
            // forward: Some(forward_sender),
            // #[cfg(feature = "sync")]
            // backward: Some(backward_receiver),
            forward: None,
            backward: None,
            should_run_weak: true,
        };

        res.grow_by(256);

        res
    }

    fn percent_full(&self) -> f64 {
        let count = self.elements.len() as f64;

        let percent = (count - self.alloc_count as f64) / count;

        assert!(percent < 1.01);

        percent
    }

    fn is_heap_full(&self) -> bool {
        self.alloc_count == 0
    }

    fn grow_by(&mut self, amount: usize) {
        // let now = crate::time::Instant::now();
        // Can probably make this a lot bigger
        let current = self.elements.len().max(amount);

        self.cursor = self.elements.len();

        self.elements.reserve(current);

        log::debug!(target: "gc", "Time to extend the heap vec");

        // let now = crate::time::Instant::now();

        // Can we pre allocate this somewhere else? Incrementally allocate the values?
        // So basically we can have the elements be allocated vs not, and just have them
        // be snatched on demand?
        self.elements.extend(
            core::iter::repeat_with(|| {
                StandardShared::new(MutContainer::new(HeapAllocated::new(T::empty())))
            })
            .take(current),
        );

        log::debug!(target: "gc", "Growing the heap by: {}", current);

        self.alloc_count += current;
        self.grow_count += 1;

        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
    }

    fn grow(&mut self) {
        self.grow_by(Self::EXTEND_CHUNK);
    }

    // Extend the heap
    fn extend_heap(&mut self) {
        self.grow();

        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
    }

    // if it points to another thing, consider marking it as unreachable?
    fn seek_to_next_free(&mut self) {
        todo!()
    }

    fn allocate(&mut self, value: T) -> HeapRef<T> {
        // Drain, moving values around...
        // is that expensive?
        let guard = &mut self.elements[self.cursor];

        // Allocate into this field
        let mut heap_guard = guard.write();

        heap_guard.value = value;

        heap_guard.reachable = true;
        let weak_ptr = StandardShared::downgrade(guard);
        drop(heap_guard);

        // self.elements[self.cursor] = pointer;
        self.alloc_count -= 1;

        // Find where to assign the next slot optimistically?
        let next_slot = self.elements[self.cursor..]
            .iter()
            .position(|x| !x.read().is_reachable());

        if let Some(next_slot) = next_slot {
            self.cursor += next_slot;

            // #[cfg(debug_assertions)]
            // {
            // assert!(!self.elements[self.cursor].read().is_reachable());
            // }
        } else {
            // TODO: Handle compaction and moving things around so the
            // cursor has a chance to actually find stuff that has been
            // freed. It would also be nice
            if self.is_heap_full() {
                log::debug!(target: "gc", "Extending the heap in `allocate`");

                // Extend the heap, move the cursor to the end
                self.extend_heap();

                // assert!(!self.elements[self.cursor].read().is_reachable());
            } else {
                // Move to the beginning.
                self.cursor = self
                    .elements
                    .iter()
                    .position(|x| !x.read().is_reachable())
                    .unwrap();

                // assert!(!self.elements[self.cursor].read().is_reachable());
            }
        }

        // assert!(!self.elements[self.cursor].read().is_reachable());

        HeapRef { inner: weak_ptr }
    }

    // Can incrementally collect with the from / to space, assuming that the collections
    // are done incrementally from the other side.
    fn collect_on_condition(
        &mut self,
        func: fn(&HeapElement<T>) -> bool,
        mut release: impl FnMut(T),
    ) -> usize {
        log::debug!(target: "gc", "Free count before weak collection: {}", self.alloc_count);
        let mut amount_dropped = 0;

        self.elements.iter_mut().for_each(|x| {
            // This is... a little gnarly? We don't want to lock each time, but it could
            // help. Allocations can now be genuinely reused since we're manipulating
            // what is inside the pointer
            if func(x) {
                let mut guard = x.write();

                if guard.reachable {
                    guard.reachable = false;
                    // Reset the values as well?
                    amount_dropped += 1;
                }
                // Queue the payload for destruction after the heap is unlocked.
                release(core::mem::replace(&mut guard.value, T::empty()));
            }
        });

        self.alloc_count += amount_dropped;
        log::debug!(target: "gc", "Free count after weak collection: {}", self.alloc_count);

        amount_dropped
    }

    // Full weak collection
    fn weak_collection(&mut self, release: impl FnMut(T)) -> usize {
        // Just mark them to be dead
        let res =
            self.collect_on_condition(|inner| StandardShared::weak_count(inner) == 0, release);
        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
        res
    }

    fn mark_all_unreachable(&mut self) {
        self.elements.iter_mut().for_each(|x| x.write().reset());
    }

    // Compact every once in a while
    // TODO: Move this on to its own thread
    fn compact(&mut self) {
        #[cfg(feature = "sync")]
        if let Some(sender) = &self.forward {
            sender.send(core::mem::take(&mut self.elements)).unwrap();
            self.elements = self.backward.as_ref().unwrap().recv().unwrap();
        } else {
            self.elements.retain(|x| x.read().is_reachable());
            self.elements.shrink_to_fit();
        }

        #[cfg(not(feature = "sync"))]
        {
            self.elements.retain(|x| x.read().is_reachable());
            self.elements.shrink_to_fit();
        }

        log::debug!(target: "gc", "Heap size after compaction: {}", self.elements.len());
        self.alloc_count = 0;
        self.grow_count = 0;
        self.extend_heap();
        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
    }

    fn strong_collection(&mut self, release: impl FnMut(T)) -> usize {
        self.collect_on_condition(|inner| !inner.read().is_reachable(), release)
    }
}

#[cfg(not(feature = "sync"))]
impl<T: HeapAble + 'static> FreeList<T> {
    // TODO: Calculate the overhead!
    // How big is this?
    const EXTEND_CHUNK: usize = 256;

    fn new() -> Self {
        #[cfg(feature = "sync")]
        let (forward_sender, backward_receiver) = spawn_background_dropper();

        let mut res = FreeList {
            elements: Vec::new(),
            cursor: 0,
            alloc_count: 0,
            grow_count: 0,
            #[cfg(feature = "sync")]
            forward: Some(forward_sender),
            #[cfg(feature = "sync")]
            backward: Some(backward_receiver),
            should_run_weak: true,
        };

        res.grow();

        res
    }

    fn percent_full(&self) -> f64 {
        let count = self.elements.len() as f64;

        let percent = (count - self.alloc_count as f64) / count;

        assert!(percent < 1.01);

        percent
    }

    fn is_heap_full(&self) -> bool {
        self.alloc_count == 0
    }

    fn grow(&mut self) {
        // let now = crate::time::Instant::now();
        // Can probably make this a lot bigger
        let current = self.elements.len().max(Self::EXTEND_CHUNK);

        self.cursor = self.elements.len();

        self.elements.reserve(current);

        log::debug!(target: "gc", "Time to extend the heap vec");

        // let now = crate::time::Instant::now();

        // Can we pre allocate this somewhere else? Incrementally allocate the values?
        // So basically we can have the elements be allocated vs not, and just have them
        // be snatched on demand?
        self.elements.extend(
            core::iter::repeat_with(|| {
                StandardShared::new(MutContainer::new(HeapAllocated::new(T::empty())))
            })
            .take(current),
        );

        log::debug!(target: "gc", "Growing the heap by: {}", current);

        self.alloc_count += current;
        self.grow_count += 1;

        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
    }

    // Extend the heap
    fn extend_heap(&mut self) {
        self.grow();

        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
    }

    // if it points to another thing, consider marking it as unreachable?
    fn seek_to_next_free(&mut self) {
        todo!()
    }

    fn allocate(&mut self, value: T) -> HeapRef<T> {
        // Drain, moving values around...
        // is that expensive?
        let guard = &mut self.elements[self.cursor];

        // Allocate into this field
        let mut heap_guard = guard.write();

        // TODO: If the guard is registered with a will executor,
        // then we shouldn't mark this value as eligible to be
        // freed?
        heap_guard.value = value;

        heap_guard.reachable = true;
        let weak_ptr = StandardShared::downgrade(&guard);
        drop(heap_guard);

        // self.elements[self.cursor] = pointer;
        self.alloc_count -= 1;

        // Find where to assign the next slot optimistically?
        let next_slot = self.elements[self.cursor..]
            .iter()
            .position(|x| !x.read().is_reachable());

        if let Some(next_slot) = next_slot {
            self.cursor += next_slot;

            // #[cfg(debug_assertions)]
            // {
            // assert!(!self.elements[self.cursor].read().is_reachable());
            // }
        } else {
            // TODO: Handle compaction and moving things around so the
            // cursor has a chance to actually find stuff that has been
            // freed. It would also be nice
            if self.is_heap_full() {
                log::debug!(target: "gc", "Extending the heap in `allocate`");

                // Extend the heap, move the cursor to the end
                self.extend_heap();

                // assert!(!self.elements[self.cursor].read().is_reachable());
            } else {
                // Move to the beginning.
                self.cursor = self
                    .elements
                    .iter()
                    .position(|x| !x.read().is_reachable())
                    .unwrap();

                // assert!(!self.elements[self.cursor].read().is_reachable());
            }
        }

        // assert!(!self.elements[self.cursor].read().is_reachable());

        HeapRef { inner: weak_ptr }
    }

    // Can incrementally collect with the from / to space, assuming that the collections
    // are done incrementally from the other side.
    fn collect_on_condition(
        &mut self,
        func: fn(&HeapElement<T>) -> bool,
        mut release: impl FnMut(T),
    ) -> usize {
        log::debug!(target: "gc", "Free count before weak collection: {}", self.alloc_count);
        let mut amount_dropped = 0;

        self.elements.iter_mut().for_each(|x| {
            // This is... a little gnarly? We don't want to lock each time, but it could
            // help. Allocations can now be genuinely reused since we're manipulating
            // what is inside the pointer
            if func(x) {
                let mut guard = x.write();

                if guard.reachable {
                    guard.reachable = false;
                    amount_dropped += 1;
                }
                // Queue the payload for destruction after the heap is unlocked.
                release(core::mem::replace(&mut guard.value, T::empty()));
            }
        });

        self.alloc_count += amount_dropped;
        log::debug!(target: "gc", "Free count after weak collection: {}", self.alloc_count);

        amount_dropped
    }

    // Full weak collection
    fn weak_collection(&mut self, release: impl FnMut(T)) -> usize {
        // Just mark them to be dead
        let res =
            self.collect_on_condition(|inner| StandardShared::weak_count(inner) == 0, release);
        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
        res
    }

    fn mark_all_unreachable(&mut self) {
        self.elements.iter_mut().for_each(|x| x.write().reset());
    }

    // Compact every once in a while
    // TODO: Move this on to its own thread
    fn compact(&mut self) {
        #[cfg(feature = "sync")]
        if let Some(sender) = &self.forward {
            sender.send(core::mem::take(&mut self.elements)).unwrap();
            self.elements = self.backward.as_ref().unwrap().recv().unwrap();
        } else {
            self.elements.retain(|x| x.read().is_reachable());
            self.elements.shrink_to_fit();
        }

        #[cfg(not(feature = "sync"))]
        {
            self.elements.retain(|x| x.read().is_reachable());
            self.elements.shrink_to_fit();
        }

        log::debug!(target: "gc", "Heap size after compaction: {}", self.elements.len());
        self.alloc_count = 0;
        self.grow_count = 0;
        self.extend_heap();
        #[cfg(debug_assertions)]
        {
            assert!(!self.elements[self.cursor].read().is_reachable());
        }
    }

    fn strong_collection(&mut self, release: impl FnMut(T)) -> usize {
        self.collect_on_condition(|inner| !inner.read().is_reachable(), release)
    }
}

impl FreeList<Vec<SteelVal>> {
    fn allocate_vec(&mut self, value: impl Iterator<Item = SteelVal>) -> HeapRef<Vec<SteelVal>> {
        // Drain, moving values around...
        // is that expensive?
        let guard = &mut self.elements[self.cursor];

        // Allocate into this field
        let mut heap_guard = guard.write();

        // Check that this fits:
        heap_guard.value.clear();

        if let (_, Some(size)) = value.size_hint() {
            let capacity = heap_guard.value.capacity();
            heap_guard
                .value
                .reserve_exact(size.saturating_sub(capacity));
        }

        for v in value {
            heap_guard.value.push(v);
        }

        heap_guard.value.shrink_to_fit();

        heap_guard.reachable = true;
        let weak_ptr = StandardShared::downgrade(guard);
        drop(heap_guard);

        // self.elements[self.cursor] = pointer;
        self.alloc_count -= 1;

        // Find where to assign the next slot optimistically?
        let next_slot = self.elements[self.cursor..]
            .iter()
            .position(|x| !x.read().is_reachable());

        if let Some(next_slot) = next_slot {
            self.cursor += next_slot;

            // #[cfg(debug_assertions)]
            // {
            // assert!(!self.elements[self.cursor].read().is_reachable());
            // }
        } else {
            // TODO: Handle compaction and moving things around so the
            // cursor has a chance to actually find stuff that has been
            // freed. It would also be nice
            if self.is_heap_full() {
                log::debug!(target: "gc", "Extending the heap in `allocate`");

                // Extend the heap, move the cursor to the end
                self.extend_heap();

                // assert!(!self.elements[self.cursor].read().is_reachable());
            } else {
                // Move to the beginning.
                self.cursor = self
                    .elements
                    .iter()
                    .position(|x| !x.read().is_reachable())
                    .unwrap();

                // assert!(!self.elements[self.cursor].read().is_reachable());
            }
        }

        // assert!(!self.elements[self.cursor].read().is_reachable());

        HeapRef { inner: weak_ptr }
    }

    fn calculate_slots_reachable(&self) -> usize {
        let mut amount = 0;
        for element in &self.elements {
            let mut guard = element.write();
            if guard.is_reachable() {
                amount += guard.value.len()
            } else {
                // Eagerly clear the value if its not reachable
                guard.value.clear();
            }
        }

        amount
    }
}

#[cfg(feature = "sync")]
fn spawn_background_dropper<T: HeapAble + Sync + Send + 'static>(
) -> (Sender<Vec<HeapElement<T>>>, Receiver<Vec<HeapElement<T>>>) {
    let (forward_sender, forward_receiver) = crossbeam_channel::bounded(0);
    let (backward_sender, backward_receiver) = crossbeam_channel::bounded(0);

    // Worker thread, capable of dropping the background values of lists
    std::thread::spawn(move || {
        let mut current: Vec<HeapElement<T>> = Vec::new();
        for mut block in forward_receiver {
            core::mem::swap(&mut current, &mut block);
            // Get the value, move on.
            backward_sender.send(block).unwrap();

            // TODO: when compacting, keep values that have been registered with a will
            // executor.
            current.retain(|x| x.read().is_reachable());
            current.shrink_to_fit();
        }
    });
    (forward_sender, backward_receiver)
}

/// The heap for steel currently uses an allocation scheme based on weak references
/// to reference counted pointers. Allocation is just a `Vec<Rc<RefCell<T>>>`, where
/// allocating simply pushes and allocates a value at the end. When we do a collection,
/// we attempt to do a small collection by just dropping any values with no weak counts
/// pointing to it.
pub struct Heap {
    #[cfg(feature = "sync")]
    collection_domain: std::sync::Arc<()>,
    count: usize,
    mark_and_sweep_queue: Vec<SteelVal>,

    maybe_memory_size: usize,

    skip_minor_collection: bool,
    memory_free_list: FreeList<SteelVal>,
    vector_free_list: FreeList<Vec<SteelVal>>,

    // Copies a collection made of values it does not own. Their destructors can reenter this
    // heap, so `SteelThread::with_heap` drops them once the heap is unlocked.
    pub(crate) released: Vec<SteelVal>,
    retained: Vec<RetainedHeap>,
    pub(crate) released_retained: Vec<RetainedHeap>,
}

// Drop the roots before their source storage, and always outside collection locks.
pub(crate) struct RetainedHeap {
    values: Vec<RootedSteelVal>,
    // Aliases root cells only while ordinarily reachable, so will keys remain weak.
    cells: Vec<RootedSteelVal>,
    heap: HeapHandle,
}

#[cfg(feature = "sync")]
unsafe impl Send for Heap {}
#[cfg(feature = "sync")]
unsafe impl Sync for Heap {}

// `FreeList::clone` keeps cell order, so the copies line up with the originals.
fn copied_cells<T: HeapAble>(
    original: &FreeList<T>,
    copy: &FreeList<T>,
) -> rustc_hash::FxHashMap<usize, HeapRef<T>> {
    debug_assert_eq!(original.elements.len(), copy.elements.len());
    original
        .elements
        .iter()
        .zip(&copy.elements)
        .map(|(original, copy)| {
            let copy = HeapRef {
                inner: StandardShared::downgrade(copy),
            };
            (StandardShared::as_ptr(original) as usize, copy)
        })
        .collect()
}

// Identities of the cells, among other values, that a collection traces from `value`,
// including custom values' children, and the traced values, which the caller releases
// outside any heap lock.
fn traced_identities(value: &SteelVal) -> (rustc_hash::FxHashSet<usize>, Vec<SteelVal>) {
    let mut queue = Vec::new();
    let mut context = MarkAndSweepContext {
        queue: &mut queue,
        stats: MarkAndSweepStats::default(),
        visited: rustc_hash::FxHashSet::default(),
        owned: None,
        trace_once: true,
        visited_lists: Default::default(),
        struct_types: Default::default(),
    };
    context.push_back(value.clone());
    context.visit();
    (context.visited, context.stats.keep_alive)
}

/// A heap's cells that a value reaches.
pub(crate) struct ReachedCells {
    values: Vec<HeapValue>,
    vectors: Vec<HeapVector>,
    // The traced values, released once the copy is rewritten.
    traced: Vec<SteelVal>,
}

/// Cells copied from another heap, and the remapper pointing at the copies.
pub(crate) struct AdoptedCells {
    values: Vec<HeapValue>,
    vectors: Vec<HeapVector>,
    remapper: HeapRemapper,
    // Dropped after `rewrite`, outside the heap locks.
    _traced: Vec<SteelVal>,
}

pub(crate) trait HeapResult {
    fn root_result(&self) -> Option<RootedSteelVal>;
}

impl HeapResult for () {
    fn root_result(&self) -> Option<RootedSteelVal> {
        None
    }
}

impl HeapResult for SteelVal {
    fn root_result(&self) -> Option<RootedSteelVal> {
        Some(self.as_rooted())
    }
}

impl HeapResult for AdoptedCells {
    fn root_result(&self) -> Option<RootedSteelVal> {
        let roots = self
            .values
            .iter()
            .map(|cell| {
                SteelVal::HeapAllocated(HeapRef {
                    inner: StandardShared::downgrade(cell),
                })
            })
            .chain(self.vectors.iter().map(|cell| {
                SteelVal::MutableVector(HeapRef {
                    inner: StandardShared::downgrade(cell),
                })
            }))
            .collect();
        Some(SteelVal::VectorV(roots).as_rooted())
    }
}

impl AdoptedCells {
    /// Point the copies and `value` at the copies. Returns the shared values that still reach
    /// the other heap.
    pub(crate) fn rewrite(self, value: &mut SteelVal) -> Vec<SteelVal> {
        self.remapper
            .rewrite_cells(&self.values, &self.vectors, [value])
    }
}

enum Remapped {
    // Contracts are remapped after the rest of the graph, so nothing else cycles back to a
    // value in progress. Reaching one anyway keeps the original.
    Pending,
    // None keeps the original value.
    Done(Option<SteelVal>),
}

enum RemapWork {
    Enter(SteelVal),
    // A suffix whose longest list was just remapped, which recorded the suffix's view.
    View(SteelVal),
    // The container and the length of the results stack before its children.
    Exit(SteelVal, usize),
}

// List nodes can share storage and an offset with different tails, so a list's key
// includes the next node. Other values use their address.
type RemapKey = (usize, usize, usize);

fn list_key(list: &List<SteelVal>) -> RemapKey {
    let (storage, offset) = list.identity_tuple();
    (storage, offset, list.next_ptr_as_usize().unwrap_or(0))
}

#[test]
fn remapped_hash_keys_use_final_cell_contents() {
    fn check(value: &SteelVal) {
        let SteelVal::HeapAllocated(cell) = value else {
            panic!("expected cell")
        };
        let SteelVal::ListV(entries) = cell.get() else {
            panic!("expected entries")
        };
        for entry in entries {
            let SteelVal::VectorV(entry) = entry else {
                panic!("expected entry")
            };
            let (SteelVal::HashMapV(map), SteelVal::HashSetV(set)) = (&entry[0], &entry[1]) else {
                panic!("expected map and set")
            };
            assert_eq!(map.get(&entry[2]), Some(&SteelVal::IntV(42)));
            assert!(set.contains(&entry[2]));
        }
    }

    for isolate in [true, false] {
        for iterator in [true, false] {
            let mut source = Heap::new();
            // Visit the tables before the cells used by their keys.
            let entries = source.allocate_without_collection(SteelVal::Void);
            let payload =
                SteelVal::HeapAllocated(source.allocate_without_collection(SteelVal::IntV(7)));
            let value = if iterator {
                SteelVal::BoxedIterator(Gc::new_mut(OpaqueIterator::from_items(
                    payload.clone(),
                    vec![payload],
                )))
            } else {
                SteelVal::StreamV(Gc::new(LazyStream {
                    initial_value: payload,
                    stream_thunk: SteelVal::Void,
                    empty_stream: false,
                }))
            };
            let cell = SteelVal::HeapAllocated(source.allocate_without_collection(value.clone()));
            let boxed = SteelVal::Boxed(Gc::new_mut(value.clone()));
            let vector =
                SteelVal::MutableVector(source.allocate_vec_without_collection(vec![value]));
            let nested_map = SteelVal::HashMapV(
                Gc::new(
                    [(SteelVal::IntV(1), cell.clone())]
                        .into_iter()
                        .collect::<super::HashMap<_, _>>(),
                )
                .into(),
            );
            let nested_set = SteelVal::HashSetV(
                Gc::new([cell.clone()].into_iter().collect::<super::HashSet<_>>()).into(),
            );
            let keys = vec![
                cell.clone(),
                boxed.clone(),
                vector,
                SteelVal::ListV([cell].into_iter().collect()),
                SteelVal::ListV([boxed].into_iter().collect()),
                nested_map,
                nested_set,
            ];
            entries.set_interior_mut(SteelVal::ListV(
                keys.into_iter()
                    .map(|key| {
                        let map = SteelVal::HashMapV(
                            Gc::new(
                                [(key.clone(), SteelVal::IntV(42))]
                                    .into_iter()
                                    .collect::<super::HashMap<_, _>>(),
                            )
                            .into(),
                        );
                        let set = SteelVal::HashSetV(
                            Gc::new([key.clone()].into_iter().collect::<super::HashSet<_>>())
                                .into(),
                        );
                        SteelVal::VectorV([map, set, key].into_iter().collect())
                    })
                    .collect(),
            ));
            let original = SteelVal::HeapAllocated(entries);
            check(&original);
            let mut root = original.clone();
            let (_destination, _retained) = if isolate {
                let (copy, remapper) = source.copy_cells();
                let retained = remapper.rewrite(&copy, [&mut root]);
                (copy, retained)
            } else {
                let mut copy = Heap::new();
                let retained = copy.adopt(source.reached_cells(&root)).rewrite(&mut root);
                (copy, retained)
            };
            check(&root);
            check(&original);
        }
    }
}

/// Rewrites references to a heap's cells into copies of those cells.
///
/// Containers are rebuilt only when a descendant changes, so untouched values keep their
/// identity. An isolated copy of a heap also copies boxes, continuations, and iterators over
/// collections like cells; an adopted result shares them. Custom values, opaque iterators,
/// futures, ports, references, native functions, and struct type properties stay shared;
/// those reaching an original cell are retained, so the caller can keep them alive.
///
/// A list's suffixes become views of the rebuilt longest list that contains them, so a
/// retained `cdr` stays `eq?` to the copy's `cdr`. Two lists that share a tail only through
/// a linked node are rebuilt separately, because im-lists cannot link a new node to an
/// existing view. For the same reason, a tail that one of the list's own elements refers
/// to, such as a closure over the list it was consed onto, is rebuilt on its own and is no
/// longer `eq?` to the copy's matching `cdr`.
pub(crate) struct HeapRemapper {
    values: rustc_hash::FxHashMap<usize, HeapRef<SteelVal>>,
    vectors: rustc_hash::FxHashMap<usize, HeapRef<Vec<SteelVal>>>,
    memo: rustc_hash::FxHashMap<RemapKey, Remapped>,
    // Copied cells whose contents still need rewriting, indexed by the copy's identity.
    pending_cells: rustc_hash::FxHashMap<usize, SteelVal>,
    boxes: Vec<GcMut<SteelVal>>,
    // Copies whose marks are remapped after the rest of the graph.
    continuations: Vec<Continuation>,
    // Copies whose root and remaining items are remapped after the rest of the graph.
    iterators: Vec<(GcMut<OpaqueIterator>, SteelVal, Vec<SteelVal>)>,
    // Closure copies whose contracts are remapped after the rest of the graph.
    contracts: Vec<(Gc<ByteCodeLambda>, SteelVal)>,
    // Each list reached as a proper suffix of a longer list, and that list.
    suffix_of: rustc_hash::FxHashMap<RemapKey, List<SteelVal>>,
    // Shared values that still reach an original cell.
    retained: Vec<SteelVal>,
    // Whether boxes, continuations, and iterators are copied. Only an isolated heap copies
    // them; an adopted result shares them like custom values, so they keep their identity.
    copy_shared_state: bool,
    // Struct types whose vtable properties were checked for original cells.
    struct_types: ReachedStructTypes,
}

impl HeapRemapper {
    fn new(
        values: rustc_hash::FxHashMap<usize, HeapRef<SteelVal>>,
        vectors: rustc_hash::FxHashMap<usize, HeapRef<Vec<SteelVal>>>,
        copy_shared_state: bool,
    ) -> Self {
        let pending_cells = values
            .values()
            .map(|cell| (cell.as_ptr_usize(), SteelVal::HeapAllocated(cell.clone())))
            .chain(
                vectors
                    .values()
                    .map(|cell| (cell.as_ptr_usize(), SteelVal::MutableVector(cell.clone()))),
            )
            .collect();
        HeapRemapper {
            values,
            vectors,
            memo: Default::default(),
            pending_cells,
            boxes: Vec::new(),
            continuations: Vec::new(),
            iterators: Vec::new(),
            contracts: Vec::new(),
            suffix_of: Default::default(),
            retained: Vec::new(),
            copy_shared_state,
            struct_types: Default::default(),
        }
    }

    /// Rewrite the copied heap and the roots that refer to the original heap. Returns the shared
    /// values that still reach the original heap.
    pub(crate) fn rewrite<'a>(
        self,
        copy: &Heap,
        roots: impl IntoIterator<Item = &'a mut SteelVal>,
    ) -> Vec<SteelVal> {
        self.rewrite_cells(
            &copy.memory_free_list.elements,
            &copy.vector_free_list.elements,
            roots,
        )
    }

    fn rewrite_cells<'a>(
        mut self,
        copied_values: &[HeapValue],
        copied_vectors: &[HeapVector],
        roots: impl IntoIterator<Item = &'a mut SteelVal>,
    ) -> Vec<SteelVal> {
        let mut roots: Vec<_> = roots.into_iter().collect();
        // Release each cell guard before remapping, since hashing keys reads cells.
        let cells: Vec<_> = copied_values
            .iter()
            .map(|cell| cell.read().value.clone())
            .collect();
        let vectors: Vec<_> = copied_vectors
            .iter()
            .map(|cell| cell.read().value.clone())
            .collect();
        self.index_lists(
            cells
                .iter()
                .chain(vectors.iter().flatten())
                .chain(roots.iter().map(|root| &**root))
                .cloned(),
        );

        for cell in copied_values {
            self.rewrite_cell(StandardShared::as_ptr(cell) as usize, false);
        }

        for cell in copied_vectors {
            self.rewrite_cell(StandardShared::as_ptr(cell) as usize, false);
        }

        for root in roots.iter_mut() {
            if let Some(value) = self.remap(root) {
                **root = value;
            }
        }

        // Copied contents and contracts can each reach more copies and contracts.
        loop {
            if let Some(copy) = self.boxes.pop() {
                self.rewrite_cell(Gc::as_ptr(&copy) as usize, false);
            } else if let Some(copy) = self.continuations.pop() {
                let mut mark = copy.inner.read().clone();
                self.remap_continuation(&mut mark);
                *copy.inner.write() = mark;
            } else if let Some((copy, root, items)) = self.iterators.pop() {
                let root = self.remap(&root).unwrap_or(root);
                let items = items
                    .into_iter()
                    .map(|item| self.remap(&item).unwrap_or(item))
                    .collect();
                *copy.write() = OpaqueIterator::from_items(root, items);
            } else if let Some((copy, contract)) = self.contracts.pop() {
                let SteelVal::CustomStruct(contract) = self.remap(&contract).unwrap_or(contract)
                else {
                    unreachable!()
                };
                copy.attach_contract_information(contract);
            } else {
                break;
            }
        }

        self.retained
    }

    // A nested rewrite, made while another remap is in progress, is deferred to the cell's
    // own turn when its contents reach a value that remap has not finished.
    fn rewrite_cell(&mut self, identity: usize, nested: bool) {
        // Remove before traversing: ordinary cycles refer to the already allocated copy.
        let Some(pending) = self.pending_cells.remove(&identity) else {
            return;
        };
        let mut deferred = false;
        match &pending {
            SteelVal::HeapAllocated(cell) => {
                let (remapped, incomplete) = self.remap_tracked(&cell.get());
                deferred = nested && incomplete;
                if let Some(value) = remapped.filter(|_| !deferred) {
                    cell.set_interior_mut(value);
                }
            }
            SteelVal::Boxed(cell) => {
                let value = cell.read().clone();
                let (remapped, incomplete) = self.remap_tracked(&value);
                deferred = nested && incomplete;
                if let Some(value) = remapped.filter(|_| !deferred) {
                    *cell.write() = value;
                }
            }
            SteelVal::MutableVector(cell) => {
                let values = cell.get();
                let mut remapped = Vec::with_capacity(values.len());
                for value in &values {
                    let (value, incomplete) = self.remap_tracked(value);
                    deferred |= nested && incomplete;
                    remapped.push(value);
                }
                if !deferred && remapped.iter().any(Option::is_some) {
                    cell.set_interior_mut(
                        values
                            .into_iter()
                            .zip(remapped)
                            .map(|(value, remapped)| remapped.unwrap_or(value))
                            .collect(),
                    );
                }
            }
            _ => unreachable!(),
        }
        if deferred {
            self.pending_cells.insert(identity, pending);
        }
    }

    // Hashing reads mutable contents, so finalize those dependencies before insertion.
    fn prepare_hash_key(&mut self, value: &SteelVal) {
        // Most keys are atoms, which have no contents to finalize.
        if !Self::may_change(value) {
            return;
        }
        let mut work = vec![value.clone()];
        let mut visited = rustc_hash::FxHashSet::default();
        while let Some(value) = work.pop() {
            if traced_identity(&value).is_some() && !visited.insert(Self::key(&value)) {
                continue;
            }
            match &value {
                SteelVal::HeapAllocated(cell) => {
                    self.rewrite_cell(cell.as_ptr_usize(), true);
                    work.push(cell.get());
                }
                SteelVal::MutableVector(cell) => {
                    self.rewrite_cell(cell.as_ptr_usize(), true);
                    work.extend(cell.get());
                }
                SteelVal::Boxed(cell) => {
                    self.rewrite_cell(Gc::as_ptr(cell) as usize, true);
                    work.push(cell.read().clone());
                }
                // These hashes do not traverse the contents remapping visits.
                SteelVal::Closure(_) | SteelVal::StreamV(_) => {}
                SteelVal::SyntaxObject(syntax) => work.extend(syntax.raw.iter().cloned()),
                value if Self::is_container(value) => work.extend(Self::children(value)),
                _ => {}
            }
        }
    }

    // A continuation's stack values, frame functions, and handlers.
    fn remap_continuation(&mut self, mark: &mut ContinuationMark) {
        let (values, frames): (_, Vec<_>) = match mark {
            ContinuationMark::Closed(closed) => (
                &mut closed.stack,
                core::iter::once(&mut closed.current_frame)
                    .chain(&mut closed.stack_frames)
                    .collect(),
            ),
            ContinuationMark::Open(open) => (
                &mut open.current_stack_values,
                vec![&mut open.current_frame],
            ),
        };
        for value in values.iter_mut() {
            if let Some(remapped) = self.remap(value) {
                *value = remapped;
            }
        }
        for frame in frames {
            if let Some(SteelVal::Closure(function)) =
                self.remap(&SteelVal::Closure(frame.function.clone()))
            {
                frame.function = function;
            }
            if let Some(handler) = frame
                .attachments
                .as_mut()
                .and_then(|attachments| attachments.handler.as_mut())
            {
                if let Some(remapped) = self.remap(handler) {
                    *handler = remapped;
                }
            }
        }
    }

    // The values a continuation holds, as `remap_continuation` reaches them.
    fn continuation_children(continuation: &Continuation) -> Vec<SteelVal> {
        let mark = continuation.inner.read();
        let (values, frames): (_, Vec<_>) = match &*mark {
            ContinuationMark::Closed(closed) => (
                &closed.stack,
                core::iter::once(&closed.current_frame)
                    .chain(&closed.stack_frames)
                    .collect(),
            ),
            ContinuationMark::Open(open) => (&open.current_stack_values, vec![&open.current_frame]),
        };
        values
            .iter()
            .cloned()
            .chain(frames.into_iter().flat_map(|frame| {
                core::iter::once(SteelVal::Closure(frame.function.clone())).chain(
                    frame
                        .attachments
                        .as_ref()
                        .and_then(|attachments| attachments.handler.clone()),
                )
            }))
            .collect()
    }

    // Shared values keep referring to the original cells, so the copy retains those that
    // reach one.
    fn retain_if_reaching(&mut self, value: &SteelVal) {
        let (identities, _traced) = traced_identities(value);
        if identities
            .iter()
            .any(|cell| self.values.contains_key(cell) || self.vectors.contains_key(cell))
        {
            self.retained.push(value.clone());
        }
    }

    // A shared value is left as is, once retained if it reaches an original cell.
    fn share(&mut self, value: &SteelVal) -> Option<Option<SteelVal>> {
        let key = Self::key(value);
        if !self.memo.contains_key(&key) {
            self.retain_if_reaching(value);
            self.memo.insert(key, Remapped::Done(None));
        }
        Some(None)
    }

    // A struct type's properties live in the vtable, which is not copied, so the copy
    // retains them while they reach an original cell and it can reach the type.
    fn retain_struct_type(&mut self, descriptor: StructTypeDescriptor) {
        if let Some(properties) = self.struct_types.properties(descriptor) {
            self.retain_if_reaching(&properties);
        }
    }

    /// Record which reachable lists are proper suffixes of longer ones. Remapping a suffix
    /// then remaps its longest list and takes the suffix as a view of the copy, whichever of
    /// the two is reached first.
    fn index_lists(&mut self, roots: impl IntoIterator<Item = SteelVal>) {
        let mut work: Vec<SteelVal> = roots.into_iter().collect();
        let mut visited = rustc_hash::FxHashSet::default();
        // Lists whose suffixes are recorded. A longer list's walk stops at one of these.
        let mut walked = rustc_hash::FxHashSet::default();

        while let Some(value) = work.pop() {
            match &value {
                // Cells are roots of this walk already.
                SteelVal::HeapAllocated(_) | SteelVal::MutableVector(_) => {}
                SteelVal::Boxed(boxed) => {
                    if visited.insert(Self::key(&value)) {
                        work.push(boxed.read().clone());
                    }
                }
                SteelVal::ContinuationFunction(continuation) => {
                    if visited.insert(Self::key(&value)) {
                        work.extend(Self::continuation_children(continuation));
                    }
                }
                // Draining the remaining items waits for remapping; they are usually the root's.
                SteelVal::BoxedIterator(iterator) => {
                    if visited.insert(Self::key(&value)) {
                        work.push(iterator.read().root.clone());
                    }
                }
                SteelVal::ListV(list) => {
                    let key = list_key(list);
                    if list.is_empty() || !visited.insert(key) {
                        continue;
                    }
                    // A list of atoms never changes, so its suffixes keep their identity.
                    if !list.iter().any(Self::may_change) {
                        continue;
                    }
                    walked.insert(key);
                    let mut suffix = list.rest();
                    while let Some(view) = suffix.take().filter(|view| !view.is_empty()) {
                        let key = list_key(&view);
                        // A tail shared with another list through a node link keeps the
                        // first list that reached it.
                        if self.suffix_of.contains_key(&key) {
                            break;
                        }
                        self.suffix_of.insert(key, list.clone());
                        if walked.contains(&key) {
                            break;
                        }
                        visited.insert(key);
                        suffix = view.rest();
                    }
                    work.extend(list.iter().cloned());
                }
                value if Self::is_container(value) && visited.insert(Self::key(value)) => {
                    work.extend(Self::graph_children(value));
                }
                _ => {}
            }
        }
    }

    // The longest list that contains this suffix.
    fn owner(&self, key: &RemapKey) -> Option<List<SteelVal>> {
        let mut head = self.suffix_of.get(key)?;
        while let Some(longer) = self.suffix_of.get(&list_key(head)) {
            head = longer;
        }
        Some(head.clone())
    }

    fn remap(&mut self, value: &SteelVal) -> Option<SteelVal> {
        self.remap_tracked(value).0
    }

    // Also whether the result depends on a value whose remapping is still in progress. Only a
    // remap nested in another, to finalize a hash key, reaches one, and such results are not
    // memoized, since they keep that value's original.
    fn remap_tracked(&mut self, value: &SteelVal) -> (Option<SteelVal>, bool) {
        let mut work = vec![RemapWork::Enter(value.clone())];
        let mut results: Vec<(Option<SteelVal>, bool)> = Vec::new();

        while let Some(item) = work.pop() {
            match item {
                RemapWork::Enter(value) => {
                    if let Some(result) = self.leaf(&value) {
                        results.push((result, false));
                        continue;
                    }

                    let key = Self::key(&value);
                    match self.memo.get(&key) {
                        Some(Remapped::Done(result)) => results.push((result.clone(), false)),
                        Some(Remapped::Pending) => results.push((None, true)),
                        None => {
                            // A suffix reached from inside its longest list's own elements
                            // is rebuilt on its own: that list's copy does not exist yet.
                            if let Some(head) = self.owner(&key).filter(|head| {
                                !matches!(self.memo.get(&list_key(head)), Some(Remapped::Pending))
                            }) {
                                work.push(RemapWork::View(value));
                                work.push(RemapWork::Enter(SteelVal::ListV(head)));
                                continue;
                            }
                            self.memo.insert(key, Remapped::Pending);
                            let children = Self::children(&value);
                            work.push(RemapWork::Exit(value, results.len()));
                            work.extend(children.into_iter().rev().map(RemapWork::Enter));
                        }
                    }
                }
                RemapWork::View(value) => {
                    if let Some((_, true)) = results.pop() {
                        results.push((None, true));
                        continue;
                    }
                    let key = Self::key(&value);
                    // An unchanged longest list leaves its suffixes unchanged.
                    let result = match self.memo.get(&key) {
                        Some(Remapped::Done(result)) => result.clone(),
                        _ => None,
                    };
                    self.memo.insert(key, Remapped::Done(result.clone()));
                    results.push((result, false));
                }
                RemapWork::Exit(value, start) => {
                    let (remapped, incomplete): (Vec<_>, Vec<_>) =
                        results.split_off(start).into_iter().unzip();
                    let incomplete = incomplete.into_iter().any(|incomplete| incomplete);
                    let contract = match &value {
                        SteelVal::Closure(closure) => closure.get_contract_information(),
                        _ => None,
                    };
                    let changed = remapped.iter().any(Option::is_some)
                        || contract
                            .as_ref()
                            .is_some_and(|contract| self.reaches_copy(contract));
                    let result = changed.then(|| {
                        let children = Self::children(&value)
                            .into_iter()
                            .zip(remapped)
                            .map(|(child, remapped)| remapped.unwrap_or(child))
                            .collect();
                        self.rebuild(&value, children)
                    });
                    if let (Some(SteelVal::Closure(copy)), Some(contract)) = (&result, contract) {
                        self.contracts.push((copy.clone(), contract));
                    }
                    match (&value, &result) {
                        // A later visit remaps it again, once that value is done.
                        _ if incomplete => {
                            self.memo.remove(&Self::key(&value));
                        }
                        (SteelVal::ListV(original), Some(SteelVal::ListV(copy))) => {
                            self.record_views(original, copy);
                        }
                        _ => {
                            self.memo
                                .insert(Self::key(&value), Remapped::Done(result.clone()));
                        }
                    }
                    results.push((result, incomplete));
                }
            }
        }

        results.pop().unwrap()
    }

    // The copy's suffixes stand in for the original's, so retained suffixes stay its views.
    fn record_views(&mut self, original: &List<SteelVal>, copy: &List<SteelVal>) {
        let mut views = Some((original.clone(), copy.clone()));
        while let Some((original, copy)) = views.take() {
            if original.is_empty() {
                break;
            }
            let key = list_key(&original);
            if !matches!(self.memo.get(&key), Some(Remapped::Done(_))) {
                self.memo
                    .insert(key, Remapped::Done(Some(SteelVal::ListV(copy.clone()))));
            }
            views = original.rest().zip(copy.rest());
        }
    }

    // Whether remapping would change this value. This walks the graph instead of remapping
    // it, because a contract can refer back to the closure being remapped.
    fn reaches_copy(&self, value: &SteelVal) -> bool {
        let mut work = vec![value.clone()];
        let mut visited = rustc_hash::FxHashSet::default();

        while let Some(value) = work.pop() {
            match &value {
                SteelVal::HeapAllocated(cell) => {
                    if self.values.contains_key(&cell.as_ptr_usize()) {
                        return true;
                    }
                }
                SteelVal::MutableVector(cell) => {
                    if self.vectors.contains_key(&cell.as_ptr_usize()) {
                        return true;
                    }
                }
                // Copied whether or not their contents change.
                SteelVal::Boxed(_)
                | SteelVal::ContinuationFunction(_)
                | SteelVal::BoxedIterator(_)
                    if self.copy_shared_state =>
                {
                    return true
                }
                SteelVal::ListV(list) if list.is_empty() => {}
                value if Self::is_container(value) => {
                    let key = Self::key(value);
                    match self.memo.get(&key) {
                        Some(Remapped::Done(Some(_))) => return true,
                        Some(Remapped::Done(None)) => {}
                        _ => {
                            if visited.insert(key) {
                                work.extend(Self::graph_children(value));
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        false
    }

    // Some(result) for values without traversed children.
    fn leaf(&mut self, value: &SteelVal) -> Option<Option<SteelVal>> {
        match value {
            // Another heap's cell stays shared like a custom value.
            SteelVal::HeapAllocated(cell) => match self.values.get(&cell.as_ptr_usize()) {
                Some(copy) => Some(Some(SteelVal::HeapAllocated(copy.clone()))),
                None => self.share(value),
            },
            SteelVal::MutableVector(cell) => match self.vectors.get(&cell.as_ptr_usize()) {
                Some(copy) => Some(Some(SteelVal::MutableVector(copy.clone()))),
                None => self.share(value),
            },
            SteelVal::Boxed(_) | SteelVal::ContinuationFunction(_) | SteelVal::BoxedIterator(_)
                if !self.copy_shared_state =>
            {
                self.share(value)
            }
            SteelVal::Boxed(boxed) => {
                let key = Self::key(value);
                if let Some(Remapped::Done(copy)) = self.memo.get(&key) {
                    return Some(copy.clone());
                }
                // The contents are remapped after the rest of the graph.
                let copy = Gc::new_mut(boxed.read().clone());
                self.boxes.push(copy.clone());
                self.pending_cells
                    .insert(Gc::as_ptr(&copy) as usize, SteelVal::Boxed(copy.clone()));
                let copy = Some(SteelVal::Boxed(copy));
                self.memo.insert(key, Remapped::Done(copy.clone()));
                Some(copy)
            }
            SteelVal::ContinuationFunction(continuation) => {
                let key = Self::key(value);
                if let Some(Remapped::Done(copy)) = self.memo.get(&key) {
                    return Some(copy.clone());
                }
                // The marks are remapped after the rest of the graph.
                let copy = Continuation {
                    inner: StandardShared::new(MutContainer::new(
                        continuation.inner.read().clone(),
                    )),
                };
                self.continuations.push(copy.clone());
                let copy = Some(SteelVal::ContinuationFunction(copy));
                self.memo.insert(key, Remapped::Done(copy.clone()));
                Some(copy)
            }
            SteelVal::BoxedIterator(iterator) => {
                let key = Self::key(value);
                if let Some(Remapped::Done(copy)) = self.memo.get(&key) {
                    return Some(copy.clone());
                }
                let mut original = iterator.write();
                let copy = match original.remaining_items() {
                    // The root and items are remapped after the rest of the graph.
                    Some(items) => {
                        let root = original.root.clone();
                        let copy =
                            Gc::new_mut(OpaqueIterator::from_items(root.clone(), items.clone()));
                        self.iterators.push((copy.clone(), root, items));
                        Some(SteelVal::BoxedIterator(copy))
                    }
                    None => {
                        drop(original);
                        self.retain_if_reaching(value);
                        None
                    }
                };
                self.memo.insert(key, Remapped::Done(copy.clone()));
                Some(copy)
            }
            SteelVal::Custom(_) => self.share(value),
            SteelVal::BoxedFunction(function) => {
                if let Some(descriptor) = struct_function_descriptor(function) {
                    self.retain_struct_type(descriptor);
                }
                Some(None)
            }
            SteelVal::CustomStruct(steel_struct) => {
                self.retain_struct_type(steel_struct.type_descriptor);
                None
            }
            SteelVal::ListV(list) if list.is_empty() => Some(None),
            value if Self::is_container(value) => None,
            _ => Some(None),
        }
    }

    fn is_container(value: &SteelVal) -> bool {
        matches!(
            value,
            SteelVal::ListV(_)
                | SteelVal::VectorV(_)
                | SteelVal::Pair(_)
                | SteelVal::HashMapV(_)
                | SteelVal::HashSetV(_)
                | SteelVal::CustomStruct(_)
                | SteelVal::Closure(_)
                | SteelVal::SyntaxObject(_)
                | SteelVal::StreamV(_)
                | SteelVal::IterV(_)
                | SteelVal::ReducerV(_)
        )
    }

    // Values whose remapped form can differ from the original.
    fn may_change(value: &SteelVal) -> bool {
        matches!(
            value,
            SteelVal::HeapAllocated(_)
                | SteelVal::MutableVector(_)
                | SteelVal::Boxed(_)
                | SteelVal::ContinuationFunction(_)
                | SteelVal::BoxedIterator(_)
        ) || Self::is_container(value)
    }

    fn key(value: &SteelVal) -> RemapKey {
        match value {
            SteelVal::ListV(list) => list_key(list),
            value => (traced_identity(value).unwrap(), 0, 0),
        }
    }

    // A closure's contract is left out: it can refer back to the closure, so it is remapped
    // after the rest of the graph and attached to the copy.
    fn children(value: &SteelVal) -> Vec<SteelVal> {
        match value {
            SteelVal::ListV(list) => list.iter().cloned().collect(),
            SteelVal::VectorV(vector) => vector.iter().cloned().collect(),
            SteelVal::Pair(pair) => vec![pair.car(), pair.cdr()],
            SteelVal::HashMapV(map) => map
                .iter()
                .flat_map(|(key, value)| [key.clone(), value.clone()])
                .collect(),
            SteelVal::HashSetV(set) => set.iter().cloned().collect(),
            SteelVal::CustomStruct(steel_struct) => steel_struct.fields.iter().cloned().collect(),
            SteelVal::Closure(closure) => closure.captures().to_vec(),
            SteelVal::SyntaxObject(syntax) => syntax
                .raw
                .iter()
                .cloned()
                .chain([syntax.syntax.clone()])
                .collect(),
            SteelVal::StreamV(stream) => {
                vec![stream.initial_value.clone(), stream.stream_thunk.clone()]
            }
            SteelVal::IterV(transducer) => transducer
                .ops
                .iter()
                .filter_map(Transducers::value)
                .cloned()
                .collect(),
            SteelVal::ReducerV(reducer) => match &**reducer {
                Reducer::ForEach(function) => vec![function.clone()],
                Reducer::Generic(generic) => {
                    vec![generic.initial_value.clone(), generic.function.clone()]
                }
                _ => Vec::new(),
            },
            _ => unreachable!(),
        }
    }

    // Every value reachable in one step, including a closure's contract.
    fn graph_children(value: &SteelVal) -> Vec<SteelVal> {
        let mut children = Self::children(value);
        if let SteelVal::Closure(closure) = value {
            children.extend(closure.get_contract_information());
        }
        children
    }

    fn rebuild(&mut self, value: &SteelVal, mut children: Vec<SteelVal>) -> SteelVal {
        match value {
            SteelVal::ListV(_) => SteelVal::ListV(children.into_iter().collect()),
            SteelVal::VectorV(_) => SteelVal::VectorV(children.into_iter().collect()),
            SteelVal::Pair(_) => {
                let cdr = children.pop().unwrap();
                let car = children.pop().unwrap();
                super::lists::Pair::cons(car, cdr).into()
            }
            SteelVal::HashMapV(_) => {
                let mut map = super::HashMap::new();
                let mut children = children.into_iter();
                while let (Some(key), Some(value)) = (children.next(), children.next()) {
                    self.prepare_hash_key(&key);
                    map.insert(key, value);
                }
                SteelVal::HashMapV(Gc::new(map).into())
            }
            SteelVal::HashSetV(_) => {
                for key in &children {
                    self.prepare_hash_key(key);
                }
                let set: super::HashSet<_> = children.into_iter().collect();
                SteelVal::HashSetV(Gc::new(set).into())
            }
            SteelVal::CustomStruct(steel_struct) => SteelVal::CustomStruct(Gc::new(
                UserDefinedStruct::new(steel_struct.type_descriptor, &children),
            )),
            // The contract is attached once it is remapped.
            SteelVal::Closure(closure) => SteelVal::Closure(Gc::new(
                closure.with_captures(children.into_iter().collect(), None),
            )),
            SteelVal::SyntaxObject(syntax) => {
                let mut copy = (**syntax).clone();
                copy.syntax = children.pop().unwrap();
                if copy.raw.is_some() {
                    copy.raw = children.pop();
                }
                SteelVal::SyntaxObject(Gc::new(copy))
            }
            SteelVal::StreamV(stream) => {
                let stream_thunk = children.pop().unwrap();
                let initial_value = children.pop().unwrap();
                SteelVal::StreamV(Gc::new(LazyStream {
                    initial_value,
                    stream_thunk,
                    empty_stream: stream.empty_stream,
                }))
            }
            SteelVal::IterV(transducer) => {
                let mut copy = (**transducer).clone();
                for (slot, child) in copy
                    .ops
                    .iter_mut()
                    .filter_map(Transducers::value_mut)
                    .zip(children)
                {
                    *slot = child;
                }
                SteelVal::IterV(Gc::new(copy))
            }
            // Only reducers that hold values have children to change.
            SteelVal::ReducerV(reducer) => SteelVal::ReducerV(Gc::new(match &**reducer {
                Reducer::ForEach(_) => Reducer::ForEach(children.pop().unwrap()),
                Reducer::Generic(_) => {
                    let function = children.pop().unwrap();
                    let initial_value = children.pop().unwrap();
                    Reducer::Generic(ReducerFunc {
                        initial_value,
                        function,
                    })
                }
                _ => unreachable!(),
            })),
            _ => unreachable!(),
        }
    }
}

// Contiguous... no good? Perhaps a free list is actually better here?
// Can reuse the allocations more effectively, and can compact where needed.
struct MemorySpace {
    memory: Vec<HeapValue>,
    vectors: Vec<HeapVector>,
}

type MemoryBlock = (Vec<HeapValue>, Vec<HeapVector>);

impl Heap {
    // Retention roots are traced only by their source heap, which a heap's address identifies
    // while a retained handle keeps it alive.
    fn retention_source(heap: &HeapHandle) -> usize {
        heap.data_ptr() as usize
    }

    pub(crate) fn retain_shared(values: Vec<SteelVal>, heap: &HeapHandle) -> RetainedHeap {
        let source = Self::retention_source(heap);
        RetainedHeap {
            values: values
                .iter()
                .map(|value| value.as_retention_root(source))
                .collect(),
            cells: Vec::new(),
            heap: heap.clone_for_storage(),
        }
    }

    pub(crate) fn retain_heap(&mut self, retained: RetainedHeap) {
        self.retained.push(retained);
    }

    /// Copies of this heap's retention, except of the heap at `except`. A heap whose values
    /// were copied from this one can reach the same retained values and cells.
    pub(crate) fn inherited_retention(&self, except: Option<&HeapHandle>) -> Vec<RetainedHeap> {
        let except = except.map(Self::retention_source);
        self.retained
            .iter()
            .filter_map(|entry| {
                let source = Self::retention_source(&entry.heap);
                (Some(source) != except).then(|| {
                    let reroot = |roots: &[RootedSteelVal]| {
                        roots
                            .iter()
                            .map(|root| root.value().as_retention_root(source))
                            .collect()
                    };
                    RetainedHeap {
                        values: reroot(&entry.values),
                        cells: reroot(&entry.cells),
                        heap: entry.heap.clone_for_storage(),
                    }
                })
            })
            .collect()
    }

    #[cfg(feature = "sync")]
    pub(crate) fn collection_domain(&self) -> std::sync::Weak<()> {
        std::sync::Arc::downgrade(&self.collection_domain)
    }

    pub(crate) fn persistent_roots(&self) -> Vec<SteelVal> {
        persistent_roots_for(Some(self as *const Heap as usize))
    }

    fn reaches_any_cell(&self, reachable: &rustc_hash::FxHashSet<usize>) -> bool {
        self.memory_free_list
            .elements
            .iter()
            .map(|cell| StandardShared::as_ptr(cell) as usize)
            .chain(
                self.vector_free_list
                    .elements
                    .iter()
                    .map(|cell| StandardShared::as_ptr(cell) as usize),
            )
            .any(|cell| reachable.contains(&cell))
    }

    pub(crate) fn prune_retained(
        &mut self,
        reachable: &rustc_hash::FxHashSet<usize>,
        ordinary: Option<&rustc_hash::FxHashSet<usize>>,
    ) {
        for mut entry in core::mem::take(&mut self.retained) {
            let source = Self::retention_source(&entry.heap);
            let aliases = match (entry.heap.try_lock(), ordinary) {
                (Some(heap), Some(ordinary)) => {
                    let known = entry
                        .cells
                        .iter()
                        .filter_map(|root| traced_identity(root.value()))
                        .collect();
                    let roots = heap.root_reached_cells(ordinary, &known, source);
                    Some((heap.reaches_any_cell(reachable), roots))
                }
                // Teardown already starts from persistent roots, which protect their cells.
                (Some(heap), None) => Some((heap.reaches_any_cell(reachable), Vec::new())),
                // Teardown needs the source only to decide whether to keep its storage.
                (None, None) => Some((true, Vec::new())),
                (None, Some(_)) => None,
            };
            let Some((keep_storage, aliases)) = aliases else {
                // Another collector may hold the source and need this heap; retry next GC.
                self.retained.push(entry);
                continue;
            };
            entry.cells.extend(aliases);
            let (live_cells, dead_cells): (Vec<_>, Vec<_>) =
                entry.cells.into_iter().partition(|root| {
                    ordinary.is_some_and(|ordinary| {
                        ordinary.contains(&traced_identity(root.value()).unwrap())
                    })
                });
            entry.cells = live_cells;
            let (live, mut dead): (Vec<_>, Vec<_>) = entry.values.into_iter().partition(|root| {
                traced_identity(root.value()).is_some_and(|identity| reachable.contains(&identity))
            });
            entry.values = live;
            dead.extend(dead_cells);
            if !dead.is_empty() {
                self.released_retained.push(RetainedHeap {
                    values: dead,
                    cells: Vec::new(),
                    heap: entry.heap.clone_for_storage(),
                });
            }
            if entry.values.is_empty() && entry.cells.is_empty() && !keep_storage {
                self.released_retained.push(entry);
            } else {
                self.retained.push(entry);
            }
        }
    }

    fn root_reached_cells(
        &self,
        reachable: &rustc_hash::FxHashSet<usize>,
        known: &rustc_hash::FxHashSet<usize>,
        source: usize,
    ) -> Vec<RootedSteelVal> {
        fn reached<T: HeapAble>(
            cells: &FreeList<T>,
            reachable: &rustc_hash::FxHashSet<usize>,
            known: &rustc_hash::FxHashSet<usize>,
        ) -> Vec<HeapRef<T>> {
            cells
                .elements
                .iter()
                .filter_map(|cell| {
                    let identity = StandardShared::as_ptr(cell) as usize;
                    (reachable.contains(&identity) && !known.contains(&identity)).then(|| HeapRef {
                        inner: StandardShared::downgrade(cell),
                    })
                })
                .collect()
        }

        reached(&self.memory_free_list, reachable, known)
            .into_iter()
            .map(SteelVal::HeapAllocated)
            .chain(
                reached(&self.vector_free_list, reachable, known)
                    .into_iter()
                    .map(SteelVal::MutableVector),
            )
            .map(|value| value.as_retention_root(source))
            .collect()
    }

    fn cell_addresses(&self) -> rustc_hash::FxHashSet<usize> {
        self.memory_free_list
            .elements
            .iter()
            .map(|cell| StandardShared::as_ptr(cell) as usize)
            .chain(
                self.vector_free_list
                    .elements
                    .iter()
                    .map(|cell| StandardShared::as_ptr(cell) as usize),
            )
            .collect()
    }

    // A closed heap keeps what the registered roots reach. A live collection keeps the same
    // values for holders outside the heap, so a value held elsewhere stays valid only while
    // its heap is alive and reaches it from its own roots or a registered root. Values meant to
    // outlive their engine are rooted, joined into another heap, or deep cloned.
    #[cfg(test)]
    pub(crate) fn trace_teardown_roots() -> (rustc_hash::FxHashSet<usize>, Vec<SteelVal>) {
        Self::trace_teardown_roots_from(persistent_roots_snapshot())
    }

    pub(crate) fn trace_teardown_roots_from(
        roots: Vec<SteelVal>,
    ) -> (rustc_hash::FxHashSet<usize>, Vec<SteelVal>) {
        let mut queue = Vec::new();
        let mut context = MarkAndSweepContext {
            queue: &mut queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            owned: None,
            trace_once: true,
            visited_lists: Default::default(),
            struct_types: Default::default(),
        };
        for root in roots {
            context.push_back(root);
        }
        context.visit();
        (context.visited, context.stats.keep_alive)
    }

    pub(crate) fn detach_unreachable(
        &mut self,
        reachable: &rustc_hash::FxHashSet<usize>,
    ) -> Vec<SteelVal> {
        let mut detached = Vec::new();
        for element in &self.memory_free_list.elements {
            if !reachable.contains(&(StandardShared::as_ptr(element) as usize)) {
                let mut guard = element.write();
                guard.reset();
                if !matches!(guard.value, SteelVal::Void) {
                    detached.push(core::mem::replace(&mut guard.value, SteelVal::Void));
                }
            }
        }
        for element in &self.vector_free_list.elements {
            if !reachable.contains(&(StandardShared::as_ptr(element) as usize)) {
                let mut guard = element.write();
                guard.reset();
                detached.extend(core::mem::take(&mut guard.value));
            }
        }
        detached
    }

    /// Copy every cell. The remapper then points copied values at the copies.
    pub(crate) fn copy_cells(&self) -> (Heap, HeapRemapper) {
        let copy = Heap {
            #[cfg(feature = "sync")]
            collection_domain: std::sync::Arc::new(()),
            count: self.count,
            mark_and_sweep_queue: Vec::with_capacity(256),
            maybe_memory_size: self.maybe_memory_size,
            skip_minor_collection: self.skip_minor_collection,
            memory_free_list: self.memory_free_list.clone(),
            vector_free_list: self.vector_free_list.clone(),
            released: Vec::new(),
            // The copied cells and shared values can reach what this heap retains.
            retained: self.inherited_retention(None),
            released_retained: Vec::new(),
        };
        let remapper = HeapRemapper::new(
            copied_cells(&self.memory_free_list, &copy.memory_free_list),
            copied_cells(&self.vector_free_list, &copy.vector_free_list),
            true,
        );
        (copy, remapper)
    }

    /// This heap's cells that `value` reaches.
    pub(crate) fn reached_cells(&self, value: &SteelVal) -> ReachedCells {
        fn reached<T: HeapAble>(
            cells: &FreeList<T>,
            reached: &rustc_hash::FxHashSet<usize>,
        ) -> Vec<HeapElement<T>> {
            cells
                .elements
                .iter()
                .filter(|cell| reached.contains(&(StandardShared::as_ptr(cell) as usize)))
                .cloned()
                .collect()
        }

        let (identities, traced) = traced_identities(value);
        ReachedCells {
            values: reached(&self.memory_free_list, &identities),
            vectors: reached(&self.vector_free_list, &identities),
            traced,
        }
    }

    /// Copy another heap's cells into this one. Their values still refer to the originals
    /// until the result rewrites them.
    pub(crate) fn adopt(&mut self, cells: ReachedCells) -> AdoptedCells {
        let mut values = rustc_hash::FxHashMap::default();
        let copied_values = cells
            .values
            .iter()
            .map(|cell| {
                let copy = self.allocate_without_collection(cell.read().value.clone());
                values.insert(StandardShared::as_ptr(cell) as usize, copy.clone());
                copy.strong_ptr()
            })
            .collect();
        let mut vectors = rustc_hash::FxHashMap::default();
        let copied_vectors = cells
            .vectors
            .iter()
            .map(|cell| {
                let copy = self.allocate_vec_without_collection(cell.read().value.clone());
                vectors.insert(StandardShared::as_ptr(cell) as usize, copy.clone());
                copy.strong_ptr()
            })
            .collect();
        AdoptedCells {
            values: copied_values,
            vectors: copied_vectors,
            // The result's boxes, continuations, and iterators can be shared with the joining
            // engine, so they are retained rather than copied.
            remapper: HeapRemapper::new(values, vectors, false),
            _traced: cells.traced,
        }
    }

    pub fn new() -> Self {
        Heap {
            #[cfg(feature = "sync")]
            collection_domain: std::sync::Arc::new(()),
            count: 0,
            // mark_and_sweep_queue: VecDeque::with_capacity(256),
            mark_and_sweep_queue: Vec::with_capacity(256),

            maybe_memory_size: 0,

            skip_minor_collection: false,

            memory_free_list: FreeList::new(),
            vector_free_list: FreeList::new(),
            released: Vec::new(),
            retained: Vec::new(),
            released_retained: Vec::new(),
        }
    }

    pub fn new_empty() -> Self {
        Heap {
            #[cfg(feature = "sync")]
            collection_domain: std::sync::Arc::new(()),
            count: 0,
            mark_and_sweep_queue: Vec::new(),
            maybe_memory_size: 0,
            skip_minor_collection: false,
            memory_free_list: FreeList::new(),
            vector_free_list: FreeList::new(),
            released: Vec::new(),
            retained: Vec::new(),
            released_retained: Vec::new(),
        }
    }

    pub fn collection<'a>(
        &mut self,
        roots: &'a [SteelVal],
        live_functions: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &'a mut Synchronizer,
        force_full: bool,
    ) {
        self.value_collection(
            &SteelVal::Void,
            roots,
            live_functions,
            globals,
            constants,
            tls,
            synchronizer,
            force_full,
        );
    }

    pub fn allocate_without_collection(&mut self, value: SteelVal) -> HeapRef<SteelVal> {
        self.memory_free_list.allocate(value)
    }

    pub fn allocate_vec_without_collection(
        &mut self,
        value: Vec<SteelVal>,
    ) -> HeapRef<Vec<SteelVal>> {
        self.vector_free_list.allocate(value)
    }

    // Clean up the values?
    pub fn allocate<'a>(
        &mut self,
        value: SteelVal,
        roots: &'a [SteelVal],
        live_functions: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &'a mut Synchronizer,
    ) -> HeapRef<SteelVal> {
        self.value_collection(
            &value,
            roots,
            live_functions,
            globals,
            constants,
            tls,
            synchronizer,
            false,
        );
        self.memory_free_list.allocate(value)
    }

    fn value_collection<'a>(
        &mut self,
        value: &SteelVal,
        roots: &'a [SteelVal],
        live_functions: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &mut Synchronizer,
        force: bool,
    ) {
        #[cfg(feature = "biased")]
        {
            steel_rc::QueueHandle::run_explicit_merge();
        }

        if self.memory_free_list.percent_full() > 0.95 || force {
            // let now = crate::time::Instant::now();
            // Attempt a weak collection
            log::debug!(target: "gc", "SteelVal gc invocation");
            self.memory_free_list
                .weak_collection(|value| self.released.push(value));

            log::debug!(target: "gc", "Memory size post weak collection: {}", self.memory_free_list.percent_full());
            // log::debug!(target: "gc", "Weak collection time: {:?}", now.elapsed());

            if self.memory_free_list.percent_full() > 0.95 || force {
                // New generation
                self.memory_free_list.mark_all_unreachable();
                self.vector_free_list.mark_all_unreachable();

                // Just reset the counter
                let stats = self.mark_and_sweep_new(
                    Some(value.clone()),
                    core::iter::empty(),
                    roots,
                    live_functions,
                    globals,
                    constants,
                    tls,
                    synchronizer,
                );

                self.memory_free_list.alloc_count = self
                    .memory_free_list
                    .elements
                    .len()
                    .saturating_sub(stats.memory_reached_count);

                self.vector_free_list.alloc_count = self
                    .vector_free_list
                    .elements
                    .len()
                    .saturating_sub(stats.vector_reached_count);

                // Estimate what that memory size is?
                if self.memory_free_list.grow_count > RESET_LIMIT {
                    // Compact the free list.
                    self.memory_free_list.compact();
                } else if self.memory_free_list.percent_full() > 0.95 {
                    self.memory_free_list.grow();
                }

                // synchronizer.resume_threads();

                log::debug!(target: "gc", "Memory size post mark and sweep: {}", self.memory_free_list.percent_full());

                // log::debug!(target: "gc", "---- TOTAL GC TIME: {:?} ----", now.elapsed());
            }
        }
    }

    pub fn allocate_vector<'a>(
        &mut self,
        values: Vec<SteelVal>,
        roots: &'a [SteelVal],
        live_functions: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &'a mut Synchronizer,
    ) -> HeapRef<Vec<SteelVal>> {
        // todo!();

        self.vector_collection(
            &values,
            roots,
            live_functions,
            globals,
            constants,
            tls,
            synchronizer,
            false,
        );

        // TOOD: Optimize this a lot!
        self.vector_free_list.allocate(values)
    }

    fn vector_collection<'a>(
        &mut self,
        values: &[SteelVal],
        roots: &'a [SteelVal],
        live_functions: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &'a mut Synchronizer,
        force: bool,
    ) {
        #[cfg(feature = "biased")]
        {
            steel_rc::QueueHandle::run_explicit_merge();
        }

        if self.vector_free_list.percent_full() > 0.50 && self.vector_free_list.should_run_weak {
            log::debug!(target: "gc", "Running weak collection because the vector free list is 50% full");
            self.vector_free_list
                .weak_collection(|values| self.released.extend(values));

            if self.vector_free_list.percent_full() > 0.30 {
                self.vector_free_list.should_run_weak = false;
            }
        }

        if self.vector_free_list.percent_full() > 0.95 || force {
            // let now = crate::time::Instant::now();
            // Attempt a weak collection
            log::debug!(target: "gc", "Vec<SteelVal> gc invocation");
            self.vector_free_list
                .weak_collection(|values| self.released.extend(values));
            self.vector_free_list.calculate_slots_reachable();
            // log::debug!(target: "gc", "Weak collection time: {:?}", now.elapsed());
            // log::debug!(target: "gc", "Weak collection time: {:?}", now.elapsed());

            if self.vector_free_list.percent_full() > 0.95 || force {
                self.vector_free_list.mark_all_unreachable();
                self.memory_free_list.mark_all_unreachable();

                let stats = self.mark_and_sweep_new(
                    None,
                    values.iter().cloned(),
                    roots,
                    live_functions,
                    globals,
                    constants,
                    tls,
                    synchronizer,
                );

                self.vector_free_list.alloc_count = self
                    .vector_free_list
                    .elements
                    .len()
                    .saturating_sub(stats.vector_reached_count);

                self.memory_free_list.alloc_count = self
                    .memory_free_list
                    .elements
                    .len()
                    .saturating_sub(stats.memory_reached_count);

                // if !self.vector_free_list.has_sufficient_memory_pressure() {
                // if self.vector_free_list.percent_full() > 0.75 {
                if self.vector_free_list.grow_count > RESET_LIMIT {
                    // Compact the free list.
                    self.vector_free_list.compact();
                } else if self.vector_free_list.percent_full() > 0.95 {
                    self.vector_free_list.grow();
                }

                self.vector_free_list.should_run_weak = true;

                log::debug!(target: "gc", "Memory size post mark and sweep: {}", self.vector_free_list.percent_full());

                // log::debug!(target: "gc", "---- TOTAL VECTOR GC TIME: {:?} ----", now.elapsed());
            }
        }
    }

    pub fn allocate_vector_iter<'a>(
        &mut self,
        values: impl Iterator<Item = SteelVal> + Clone,
        roots: &'a [SteelVal],
        live_functions: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &'a mut Synchronizer,
    ) -> HeapRef<Vec<SteelVal>> {
        #[cfg(feature = "biased")]
        {
            steel_rc::QueueHandle::run_explicit_merge();
        }

        if self.vector_free_list.percent_full() > 0.50 && self.vector_free_list.should_run_weak {
            self.vector_free_list
                .weak_collection(|values| self.released.extend(values));

            if self.vector_free_list.percent_full() > 0.30 {
                self.vector_free_list.should_run_weak = false;
            }
        }

        if self.vector_free_list.percent_full() > 0.95 {
            // let now = crate::time::Instant::now();
            // Attempt a weak collection
            log::debug!(target: "gc", "Vec<SteelVal> gc invocation");
            self.vector_free_list
                .weak_collection(|values| self.released.extend(values));
            self.vector_free_list.calculate_slots_reachable();
            // log::debug!(target: "gc", "Weak collection time: {:?}", now.elapsed());
            // log::debug!(target: "gc", "Weak collection time: {:?}", now.elapsed());

            if self.vector_free_list.percent_full() > 0.95 {
                self.vector_free_list.mark_all_unreachable();
                self.memory_free_list.mark_all_unreachable();

                let stats = self.mark_and_sweep_new(
                    None,
                    values.clone(),
                    roots,
                    live_functions,
                    globals,
                    constants,
                    tls,
                    synchronizer,
                );

                self.vector_free_list.alloc_count = self
                    .vector_free_list
                    .elements
                    .len()
                    .saturating_sub(stats.vector_reached_count);

                self.memory_free_list.alloc_count = self
                    .memory_free_list
                    .elements
                    .len()
                    .saturating_sub(stats.memory_reached_count);

                // if self.vector_free_list.percent_full() > 0.75 {
                if self.vector_free_list.grow_count > RESET_LIMIT {
                    // Compact the free list.
                    self.vector_free_list.compact();
                } else if self.vector_free_list.percent_full() > 0.95 {
                    self.vector_free_list.grow();
                }

                self.vector_free_list.should_run_weak = true;

                log::debug!(target: "gc", "Memory size post mark and sweep: {}", self.vector_free_list.percent_full());

                // log::debug!(target: "gc", "---- TOTAL VECTOR GC TIME: {:?} ----", now.elapsed());
            }
        }

        self.vector_free_list.allocate_vec(values)
    }

    fn mark_and_sweep_new<'a>(
        &mut self,
        root_value: Option<SteelVal>,
        root_vector: impl Iterator<Item = SteelVal>,
        roots: &'a [SteelVal],
        function_stack: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &'a [SteelVal],
        constants: &ConstantMap,
        tls: &'a [SteelVal],
        synchronizer: &mut Synchronizer,
    ) -> MarkAndSweepStats {
        let mut stats = self.mark(
            root_value,
            root_vector,
            roots,
            function_stack,
            globals,
            constants,
            tls,
            synchronizer,
        );
        self.released.append(&mut stats.keep_alive);

        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        #[cfg(feature = "sync")]
        {
            GLOBAL_ROOTS.lock().unwrap().increment_generation();
        }

        #[cfg(not(feature = "sync"))]
        {
            ROOTS.with(|x| x.borrow_mut().increment_generation());
        }

        #[cfg(feature = "profiling")]
        log::debug!(target: "gc", "Sweep: Time taken: {:?}", now.elapsed());

        synchronizer.resume_threads();

        stats

        // object_count.saturating_sub(amount_freed)
        // 0
    }

    fn mark<'a>(
        &mut self,
        root_value: Option<SteelVal>,
        root_vector: impl Iterator<Item = SteelVal>,
        roots: &[SteelVal],
        function_stack: impl Iterator<Item = &'a ByteCodeLambda>,
        globals: &[SteelVal],
        constants: &ConstantMap,
        tls: &[SteelVal],
        synchronizer: &mut Synchronizer,
    ) -> MarkAndSweepStats {
        log::debug!(target: "gc", "Marking the heap");

        #[cfg(feature = "profiling")]
        let now = crate::time::Instant::now();

        synchronizer.stop_threads();
        let owned = self.cell_addresses();
        let heap = self as *const Heap as usize;
        let mut context = MarkAndSweepContext {
            queue: &mut self.mark_and_sweep_queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            owned: Some(&owned),
            trace_once: false,
            visited_lists: Default::default(),
            struct_types: Default::default(),
        };

        unsafe {
            synchronizer.enumerate_stacks(&mut context);
        }

        if let Some(root_value) = root_value {
            context.push_back(root_value);
        }

        for value in root_vector {
            context.push_back(value.clone());
        }

        for root in tls {
            context.push_back(root.clone());
        }

        constants.trace(&mut context);
        // Read once the other threads have stopped: a thread can register a root right up to
        // its safepoint, and its stack then no longer holds the value.
        for root in persistent_roots_for(Some(heap)) {
            context.push_back(root);
        }

        log::debug!(target: "gc", "Roots size: {}", roots.len());
        for root in roots {
            context.push_back(root.clone());
        }

        log::debug!(target: "gc", "Globals size: {}", globals.len());
        for root in globals {
            context.push_back(root.clone());
        }

        #[cfg(feature = "sync")]
        let mut reachable = rustc_hash::FxHashSet::default();
        for function in function_stack {
            #[cfg(feature = "sync")]
            reachable.insert(function as *const ByteCodeLambda as usize);
            for value in function.captures() {
                context.push_back(value.clone());
            }
        }

        // Each confined interpreter has its own memory budget. Mark on its current
        // thread instead of allocating a machine-sized worker pool at the first GC.
        #[cfg(feature = "sync")]
        let (stats, ordinary) = {
            let queue = crossbeam_queue::SegQueue::new();
            let mut local_queue = Vec::with_capacity(4096);
            let mut marker = MarkAndSweepContextRefQueue {
                collection_domain: Some(&self.collection_domain),
                queue: &queue,
                local_queue: &mut local_queue,
                stats: MarkAndSweepStats::default(),
                visited: rustc_hash::FxHashSet::default(),
                will_executors: Vec::new(),
                reachable,
                owned: &owned,
                struct_types: core::mem::take(&mut context.struct_types),
            };
            for value in context.queue.iter() {
                marker.push_back(value);
            }
            marker.visit();
            let ordinary = (!self.retained.is_empty()).then(|| marker.reachable.clone());
            marker.retain_wills();
            // The marker records reachability in its own set, not in its stats.
            marker.stats.reachable = core::mem::take(&mut marker.reachable);
            // A root snapshot can hold the last reference to a root released meanwhile.
            self.released.append(context.queue);
            self.released.append(&mut context.stats.keep_alive);
            (marker.stats, ordinary)
        };
        // Without wills, everything traced is ordinarily reachable.
        #[cfg(not(feature = "sync"))]
        let (stats, ordinary) = {
            context.visit();
            (context.stats, None::<rustc_hash::FxHashSet<usize>>)
        };
        self.prune_retained(
            &stats.reachable,
            Some(ordinary.as_ref().unwrap_or(&stats.reachable)),
        );
        // Free slots must release their payloads even if no later allocation reuses them.
        self.memory_free_list
            .strong_collection(|value| self.released.push(value));
        self.vector_free_list
            .strong_collection(|values| self.released.extend(values));
        stats
    }
}

pub trait HeapAble: Clone + core::fmt::Debug + PartialEq + Eq {
    fn empty() -> Self;
}
impl HeapAble for SteelVal {
    fn empty() -> Self {
        SteelVal::Void
    }
}

impl HeapAble for Vec<SteelVal> {
    fn empty() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug)]
pub struct HeapRef<T: HeapAble> {
    pub(crate) inner: WeakShared<MutContainer<HeapAllocated<T>>>,
}

impl<T: HeapAble> HeapRef<T> {
    #[inline(always)]
    pub fn get(&self) -> T {
        self.inner.upgrade().unwrap().read().value.clone()
    }

    /// Get the value if the pointer is still valid.
    /// If this is the only thing pointing at it, then we need to drop it.
    pub(crate) fn maybe_get_from_weak(&self) -> Option<T> {
        let inner = self.inner.upgrade()?;

        // Check if this thing is reachable? How?
        if StandardShared::weak_count(&inner) == 1 {
            // We can go ahead and nuke this since we're
            // the only things pointing to it
            let mut value = inner.write();

            if value.is_reachable() {
                Some(value.value.clone())
            } else {
                value.reachable = false;
                value.value = T::empty();
                None
            }
        } else {
            // Get the inner value on this, assuming we are calling
            // this just from the heap ref. Anywhere else, we'll want
            // to eliminate this?
            Some(inner.read().value.clone())
        }
    }

    pub fn borrow<O>(&self, thunk: impl FnOnce(&T) -> O) -> O {
        let value = self.inner.upgrade().unwrap();
        let value = value.read();
        thunk(&value.value)
    }

    pub fn as_ptr_usize(&self) -> usize {
        self.inner.as_ptr() as usize
    }

    pub fn set(&mut self, value: T) -> T {
        let inner = self.inner.upgrade().unwrap();

        let ret = { inner.read().value.clone() };

        inner.write().value = value;
        ret
    }

    pub fn set_and_return(&self, value: T) -> T {
        let inner = self.inner.upgrade().unwrap();

        let mut guard = inner.write();
        core::mem::replace(&mut guard.value, value)
    }

    pub(crate) fn set_interior_mut(&self, value: T) -> T {
        let inner = self.inner.upgrade().unwrap();

        let ret = { inner.read().value.clone() };

        inner.write().value = value;
        ret
    }

    pub(crate) fn strong_ptr(&self) -> StandardSharedMut<HeapAllocated<T>> {
        self.inner.upgrade().unwrap()
    }

    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        WeakShared::ptr_eq(&self.inner, &other.inner)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeapAllocated<T: Clone + core::fmt::Debug + PartialEq + Eq> {
    pub(crate) reachable: bool,
    pub(crate) finalizer: bool,
    pub(crate) value: T,
}

// // Use atomic bools, and then store the value
// // as a Cell?
// pub struct Foo<T: Clone + core::fmt::Debug + PartialEq + Eq> {
//     pub(crate) reachable: AtomicBool,
//     pub(crate) finalizer: AtomicBool,
//     pub(crate) value: T,
// }
// type TestThing = hybrid_rc::Arc<String>;

#[test]
fn check_size_of_heap_allocated_value() {
    println!("{:?}", core::mem::size_of::<HeapAllocated<SteelVal>>());
}

impl<T: Clone + core::fmt::Debug + PartialEq + Eq> HeapAllocated<T> {
    pub fn new(value: T) -> Self {
        Self {
            reachable: false,
            finalizer: false,
            value,
        }
    }

    pub fn is_reachable(&self) -> bool {
        self.reachable
    }

    pub(crate) fn mark_reachable(&mut self) {
        self.reachable = true;
    }

    pub(crate) fn reset(&mut self) {
        self.reachable = false;
    }
}

pub struct MarkAndSweepContext<'a> {
    queue: &'a mut Vec<SteelVal>,
    stats: MarkAndSweepStats,
    visited: rustc_hash::FxHashSet<usize>,
    // None means traversal only; foreign cells never share collection marks.
    owned: Option<&'a rustc_hash::FxHashSet<usize>>,
    // Teardown and copy scans trace each value once, deduplicating as values are pushed.
    trace_once: bool,
    // Lists traced once, by their whole node.
    visited_lists: rustc_hash::FxHashSet<RemapKey>,
    struct_types: ReachedStructTypes,
}

impl<'a> MarkAndSweepContext<'a> {
    // Only collections read reachability; traversal-only scans track `visited` instead.
    fn record_reachable(&mut self, identity: usize) {
        if self.owned.is_some() {
            self.stats.reachable.insert(identity);
        }
    }

    // Values that can recreate a struct type's instances keep its properties reachable.
    pub(crate) fn visit_struct_type(&mut self, descriptor: StructTypeDescriptor) {
        if let Some(properties) = self.struct_types.properties(descriptor) {
            self.push_back(properties);
        }
    }

    pub(crate) fn mark_heap_reference(
        &mut self,
        heap_ref: &StandardSharedMut<HeapAllocated<SteelVal>>,
    ) {
        let identity = StandardShared::as_ptr(heap_ref) as usize;
        self.record_reachable(identity);
        if self.owned.is_some_and(|owned| owned.contains(&identity)) {
            let mut guard = heap_ref.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
            self.stats.memory_reached_count += 1;
        } else if !self.trace_once && !self.visited.insert(identity) {
            return;
        }

        self.push_back(heap_ref.read().value.clone());
    }

    // Visit the heap vector, mark it as visited!
    pub(crate) fn mark_heap_vector(
        &mut self,
        heap_vector: &StandardSharedMut<HeapAllocated<Vec<SteelVal>>>,
    ) {
        let identity = StandardShared::as_ptr(heap_vector) as usize;
        self.record_reachable(identity);
        if self.owned.is_some_and(|owned| owned.contains(&identity)) {
            let mut guard = heap_vector.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
            self.stats.vector_reached_count += 1;
        } else if !self.trace_once && !self.visited.insert(identity) {
            return;
        }

        for value in heap_vector.read().value.iter() {
            self.push_back(value.clone());
        }
    }
}

#[derive(Debug, Clone, Default)]
struct MarkAndSweepStats {
    object_count: usize,
    memory_reached_count: usize,
    vector_reached_count: usize,
    keep_alive: Vec<SteelVal>,
    reachable: rustc_hash::FxHashSet<usize>,
}

impl core::ops::Add for MarkAndSweepStats {
    type Output = MarkAndSweepStats;

    fn add(mut self, rhs: Self) -> Self::Output {
        self.object_count += rhs.object_count;
        self.memory_reached_count += rhs.memory_reached_count;
        self.vector_reached_count += rhs.vector_reached_count;
        self.reachable.extend(rhs.reachable);
        self
    }
}

#[cfg(feature = "sync")]
pub struct MarkAndSweepContextRefQueue<'a> {
    collection_domain: Option<&'a std::sync::Arc<()>>,
    // Thread local queue + larger queue when it runs out?
    // Try to push on to local queue first.
    local_queue: &'a mut Vec<SteelValPointer>,
    queue: &'a crossbeam_queue::SegQueue<SteelValPointer>,
    stats: MarkAndSweepStats,
    visited: rustc_hash::FxHashSet<usize>,
    will_executors: Vec<&'a MutContainer<Box<dyn CustomType>>>,
    reachable: rustc_hash::FxHashSet<usize>,
    owned: &'a rustc_hash::FxHashSet<usize>,
    struct_types: ReachedStructTypes,
}

#[cfg(feature = "sync")]
impl<'a> MarkAndSweepContextRefQueue<'a> {
    fn retain_wills(&mut self) {
        // Retention must not change eligibility, even for executors discovered later.
        let reachable = std::mem::take(&mut self.reachable);
        let mut processed = 0;
        while processed < self.will_executors.len() {
            let end = self.will_executors.len();
            // Record eligibility before retention changes the heap's reachability marks.
            for custom in &self.will_executors[processed..end] {
                let guard = custom.read();
                let executor = guard.as_any_ref().downcast_ref::<WillExecutor>().unwrap();
                let mut values = executor.values.lock().unwrap();
                values.extend(executor.incoming.try_iter().map(Some));
                for pending in values.iter_mut().flatten() {
                    let key = pending.pair.car_ref();
                    let local = match key {
                        SteelVal::HeapAllocated(cell) => self.owned.contains(&cell.as_ptr_usize()),
                        SteelVal::MutableVector(cell) => self.owned.contains(&cell.as_ptr_usize()),
                        _ => self
                            .collection_domain
                            .zip(pending.collection_domain.as_ref())
                            .is_some_and(|(domain, registered)| {
                                core::ptr::eq(
                                    std::sync::Weak::as_ptr(registered),
                                    std::sync::Arc::as_ptr(domain),
                                )
                            }),
                    };
                    pending.ready |= if local {
                        traced_identity(key).map_or_else(
                            || pending.is_unreachable(),
                            |identity| !reachable.contains(&identity),
                        )
                    } else {
                        pending.is_unreachable()
                    };
                }
            }
            for index in processed..end {
                let custom = self.will_executors[index];
                self.visit_custom_children(custom);
            }
            self.visit();
            processed = end;
        }
        // Merge what retention reached into the ordinary set, which is usually far larger.
        let retained = core::mem::replace(&mut self.reachable, reachable);
        self.reachable.extend(retained);
    }

    fn visit_custom_children(&mut self, custom_type: &MutContainer<Box<dyn CustomType>>) {
        let mut queue = Vec::new();
        let mut temporary_queue = MarkAndSweepContext {
            queue: &mut queue,
            stats: MarkAndSweepStats::default(),
            visited: core::mem::take(&mut self.visited),
            owned: Some(self.owned),
            trace_once: false,
            visited_lists: Default::default(),
            struct_types: core::mem::take(&mut self.struct_types),
        };

        visit_custom_children(custom_type, &mut temporary_queue);
        self.visited = temporary_queue.visited;
        self.struct_types = temporary_queue.struct_types;

        self.stats.memory_reached_count += temporary_queue.stats.memory_reached_count;
        self.stats.object_count += temporary_queue.stats.object_count;
        self.stats.vector_reached_count += temporary_queue.stats.vector_reached_count;
        self.reachable.extend(temporary_queue.stats.reachable);
        self.stats
            .keep_alive
            .append(&mut temporary_queue.stats.keep_alive);

        for value in queue {
            self.push_back(&value);
            self.save(value);
        }
    }

    pub(crate) fn mark_heap_reference(
        &mut self,
        heap_ref: &StandardSharedMut<HeapAllocated<SteelVal>>,
    ) {
        let identity = StandardShared::as_ptr(heap_ref) as usize;
        self.reachable.insert(identity);
        let local = self.owned.contains(&identity);
        if local {
            let mut guard = heap_ref.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
            self.stats.memory_reached_count += 1;
        } else if !self.visited.insert(identity) {
            return;
        }

        let guard = heap_ref.read();
        // Local payloads are protected by the heap lock and worker safepoints.
        if !local {
            self.save(guard.value.clone());
        }
        self.push_back(&guard.value);
    }

    // Visit the heap vector, mark it as visited!
    pub(crate) fn mark_heap_vector(
        &mut self,
        heap_vector: &StandardSharedMut<HeapAllocated<Vec<SteelVal>>>,
    ) {
        let identity = StandardShared::as_ptr(heap_vector) as usize;
        self.reachable.insert(identity);
        let local = self.owned.contains(&identity);
        if local {
            let mut guard = heap_vector.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
            self.stats.vector_reached_count += 1;
        } else if !self.visited.insert(identity) {
            return;
        }

        for value in heap_vector.read().value.iter() {
            if !local {
                self.save(value.clone());
            }
            self.push_back(value);
        }
    }

    pub(crate) fn save(&mut self, value: SteelVal) {
        self.stats.keep_alive.push(value);
    }
}

// TODO: @Matt
// Eventually once we decouple the RwLock from the dyn Custom variant, we can get rid of this
//
// This issue is that the GC will block on these values because they're mutably referenced,
// so during the mark phase, the gc visitor hits a mutably referenced value over FFI and blocks,
// but the value _must_ be mutably blocked to avoid double borrows. This ends up in a funny
// situation where any blocking call just stops the GC.
//
// To avoid this, we store a stack of the addresses that we visit and just expose those
// to the gc so that it can skip these. Values passed over FFI are special; they do not
// have the same restrictions since they can't actually hold steel values.
#[cfg(feature = "dylibs")]
pub(crate) mod ffi_borrows {
    use parking_lot::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Weak};

    const CAPACITY: usize = 32;

    struct ThreadBorrows {
        len: AtomicUsize,
        addresses: [AtomicUsize; CAPACITY],
    }

    static THREADS: Mutex<Vec<Weak<ThreadBorrows>>> = Mutex::new(Vec::new());

    thread_local! {
        static BORROWS: Arc<ThreadBorrows> = {
            let borrows = Arc::new(ThreadBorrows {
                len: AtomicUsize::new(0),
                addresses: [const { AtomicUsize::new(0) }; CAPACITY],
            });

            let mut threads = THREADS.lock();
            threads.retain(|thread| thread.strong_count() > 0);
            threads.push(Arc::downgrade(&borrows));

            borrows
        };
    }

    pub(crate) fn push(address: usize) -> bool {
        BORROWS.with(|borrows| {
            let len = borrows.len.load(Ordering::Relaxed);
            if len == CAPACITY {
                return false;
            }

            borrows.addresses[len].store(address, Ordering::Release);
            borrows.len.store(len + 1, Ordering::Release);
            true
        })
    }

    pub(crate) fn pop(count: usize) {
        BORROWS.with(|borrows| {
            let len = borrows.len.load(Ordering::Relaxed);
            borrows.len.store(len - count, Ordering::Release);
        })
    }

    #[cfg(feature = "sync")]
    pub(crate) fn held_by_current_thread(address: usize) -> bool {
        BORROWS.with(|borrows| {
            let len = borrows.len.load(Ordering::Relaxed);
            len == CAPACITY
                || borrows.addresses[..len]
                    .iter()
                    .any(|x| x.load(Ordering::Relaxed) == address)
        })
    }

    #[cfg(feature = "sync")]
    pub(crate) fn contains(address: usize) -> bool {
        THREADS.lock().iter().any(|thread| {
            let Some(thread) = thread.upgrade() else {
                return false;
            };

            let len = thread.len.load(Ordering::Acquire);
            thread.addresses[..len]
                .iter()
                .any(|x| x.load(Ordering::Acquire) == address)
        })
    }
}

#[cfg(all(feature = "sync", feature = "dylibs"))]
fn read_custom_type(
    custom_type: &MutContainer<Box<dyn CustomType>>,
) -> Option<crate::gc::shared::ScopedReadContainer<'_, Box<dyn CustomType>>> {
    let address = custom_type as *const _ as usize;

    loop {
        if let Some(guard) = custom_type.try_read() {
            return Some(guard);
        }

        if ffi_borrows::contains(address) {
            return None;
        }

        std::thread::yield_now();
    }
}

#[cfg(not(all(feature = "sync", feature = "dylibs")))]
fn read_custom_type(
    custom_type: &MutContainer<Box<dyn CustomType>>,
) -> Option<crate::gc::shared::ScopedReadContainer<'_, Box<dyn CustomType>>> {
    #[cfg(feature = "sync")]
    return Some(custom_type.read());

    #[cfg(not(feature = "sync"))]
    Some(custom_type.borrow())
}

fn visit_custom_children(
    custom_type: &MutContainer<Box<dyn CustomType>>,
    context: &mut MarkAndSweepContext,
) {
    if let Some(custom_type) = read_custom_type(custom_type) {
        custom_type.visit_children(context);
    }
}

impl<'a> BreadthFirstSearchSteelValVisitor for MarkAndSweepContext<'a> {
    type Output = ();

    fn default_output(&mut self) -> Self::Output {}

    // TODO: Do this in parallel, if possible?
    fn pop_front(&mut self) -> Option<SteelVal> {
        self.queue.pop()
    }

    fn push_back(&mut self, value: SteelVal) {
        if let Some(identity) = traced_identity(&value) {
            self.record_reachable(identity);
        }
        if self.trace_once {
            // List slices can share an address while exposing different elements, so a list
            // is identified by its whole node.
            let first = match &value {
                SteelVal::ListV(list) => Some(self.visited_lists.insert(list_key(list))),
                value => traced_identity(value).map(|identity| self.visited.insert(identity)),
            };
            match first {
                Some(false) => return,
                // A traced value's address must not be reused during the pass.
                Some(true) => self.stats.keep_alive.push(value.clone()),
                None => {}
            }
        }
        self.stats.object_count += 1;

        // TODO: Determine if all numbers should push back.
        match &value {
            SteelVal::BoxedFunction(function) => {
                if let Some(properties) = self.struct_types.function_properties(function) {
                    self.push_back(properties);
                }
                // Native functions and futures can run arbitrary code when dropped, and
                // another thread can release the original meanwhile.
                #[cfg(feature = "sync")]
                self.stats.keep_alive.push(value);
            }
            SteelVal::FutureFunc(_) | SteelVal::FutureV(_) => {
                #[cfg(feature = "sync")]
                self.stats.keep_alive.push(value);
            }
            SteelVal::BoolV(_)
            | SteelVal::NumV(_)
            | SteelVal::IntV(_)
            | SteelVal::CharV(_)
            | SteelVal::Void
            | SteelVal::StringV(_)
            | SteelVal::FuncV(_)
            | SteelVal::SymbolV(_)
            | SteelVal::MutFunc(_)
            | SteelVal::BuiltIn(_)
            | SteelVal::ByteVector(_)
            | SteelVal::BigNum(_) => (),
            _ => {
                self.queue.push(value);
            }
        }
    }

    fn visit_bytevector(&mut self, _bytevector: crate::rvals::SteelByteVector) -> Self::Output {}
    fn visit_bignum(&mut self, _: Gc<BigInt>) -> Self::Output {}
    fn visit_complex(&mut self, _: Gc<SteelComplex>) -> Self::Output {}
    fn visit_bool(&mut self, _boolean: bool) -> Self::Output {}
    fn visit_boxed_function(&mut self, _function: Gc<BoxedDynFunction>) -> Self::Output {}
    // TODO: Revisit this when the boxed iterator is cleaned up
    fn visit_boxed_iterator(&mut self, iterator: GcMut<OpaqueIterator>) -> Self::Output {
        self.push_back(iterator.read().root.clone());
    }
    fn visit_boxed_value(&mut self, boxed_value: GcMut<SteelVal>) -> Self::Output {
        self.push_back(boxed_value.read().clone());
    }

    fn visit_builtin_function(&mut self, _function: BuiltInSignature) -> Self::Output {}

    fn visit_char(&mut self, _c: char) -> Self::Output {}
    fn visit_closure(&mut self, closure: Gc<ByteCodeLambda>) -> Self::Output {
        // for heap_ref in closure.heap_allocated.borrow().iter() {
        //     self.mark_heap_reference(&heap_ref.strong_ptr())
        // }

        for capture in closure.captures() {
            self.push_back(capture.clone());
        }

        if let Some(contract) = closure.get_contract_information().as_ref() {
            self.push_back(contract.clone());
        }
    }
    fn visit_continuation(&mut self, continuation: Continuation) -> Self::Output {
        // TODO: Don't clone this here!
        let continuation = (*continuation.inner.read()).clone();

        match continuation {
            ContinuationMark::Closed(continuation) => {
                for value in continuation.stack {
                    self.push_back(value);
                }

                for value in &continuation.current_frame.function.captures {
                    self.push_back(value.clone());
                }

                for frame in continuation.stack_frames {
                    for value in &frame.function.captures {
                        self.push_back(value.clone());
                    }

                    // if let Some(handler) = &frame.handler {
                    //     self.push_back((*handler.as_ref()).clone());
                    // }

                    if let Some(handler) =
                        frame.attachments.as_ref().and_then(|x| x.handler.clone())
                    {
                        self.push_back(handler);
                    }
                }
            }

            ContinuationMark::Open(_) => {
                /*
                for value in &continuation.current_stack_values {
                    self.push_back(value.clone());
                }

                for value in &continuation.current_frame.function.captures {
                    self.push_back(value.clone());
                }
                */
            }
        }
    }
    // TODO: Come back to this
    fn visit_custom_type(&mut self, custom_type: GcMut<Box<dyn CustomType>>) -> Self::Output {
        if !self.trace_once && !self.visited.insert(custom_type.as_ptr() as usize) {
            return;
        }
        let Some(custom_type) = read_custom_type(&custom_type) else {
            return;
        };
        if let Some(properties) = self
            .struct_types
            .descriptor_properties(custom_type.as_ref())
        {
            self.push_back(properties);
        }
        custom_type.visit_children(self);
    }

    fn visit_float(&mut self, _float: f64) -> Self::Output {}

    fn visit_function_pointer(&mut self, _ptr: FunctionSignature) -> Self::Output {}

    fn visit_future(&mut self, _future: Gc<FutureResult>) -> Self::Output {}

    fn visit_future_function(&mut self, _function: BoxedAsyncFunctionSignature) -> Self::Output {}

    fn visit_hash_map(&mut self, hashmap: SteelHashMap) -> Self::Output {
        if !self.trace_once && !self.visited.insert(hashmap.0.as_ptr() as usize) {
            return;
        }
        for (key, value) in hashmap.iter() {
            self.push_back(key.clone());
            self.push_back(value.clone());
        }
    }

    fn visit_hash_set(&mut self, hashset: SteelHashSet) -> Self::Output {
        for value in hashset.iter() {
            self.push_back(value.clone());
        }
    }

    fn visit_heap_allocated(&mut self, heap_ref: HeapRef<SteelVal>) -> Self::Output {
        if let Some(heap_ref) = heap_ref.inner.upgrade() {
            self.mark_heap_reference(&heap_ref);
        }
    }

    fn visit_immutable_vector(&mut self, vector: SteelVector) -> Self::Output {
        for value in vector.iter() {
            self.push_back(value.clone());
        }
    }
    fn visit_int(&mut self, _int: isize) -> Self::Output {}
    fn visit_rational(&mut self, _: Rational32) -> Self::Output {}
    fn visit_bigrational(&mut self, _: Gc<BigRational>) -> Self::Output {}

    // Borrows the elements: consuming a list builds an empty one through im-lists'
    // thread-local storage, which a teardown trace can outlive.
    fn visit_list(&mut self, list: List<SteelVal>) -> Self::Output {
        for value in list.iter() {
            self.push_back(value.clone());
        }
    }

    fn visit_mutable_function(&mut self, _function: MutFunctionSignature) -> Self::Output {}

    fn visit_mutable_vector(&mut self, vector: HeapRef<Vec<SteelVal>>) -> Self::Output {
        if let Some(vector) = vector.inner.upgrade() {
            self.mark_heap_vector(&vector);
        }
    }

    fn visit_port(&mut self, _port: SteelPort) -> Self::Output {}

    fn visit_reducer(&mut self, reducer: Gc<Reducer>) -> Self::Output {
        match reducer.as_ref().clone() {
            Reducer::ForEach(f) => self.push_back(f),
            Reducer::Generic(rf) => {
                self.push_back(rf.initial_value);
                self.push_back(rf.function);
            }
            _ => {}
        }
    }

    // TODO: Revisit this
    fn visit_reference_value(&mut self, _reference: Gc<OpaqueReference<'static>>) -> Self::Output {}

    fn visit_steel_struct(&mut self, steel_struct: Gc<UserDefinedStruct>) -> Self::Output {
        if let Some(properties) = self.struct_types.properties(steel_struct.type_descriptor) {
            self.push_back(properties);
        }
        for field in steel_struct.fields.iter() {
            self.push_back(field.clone());
        }
    }

    fn visit_stream(&mut self, stream: Gc<LazyStream>) -> Self::Output {
        self.push_back(stream.initial_value.clone());
        self.push_back(stream.stream_thunk.clone());
    }

    fn visit_string(&mut self, _string: SteelString) -> Self::Output {}

    fn visit_symbol(&mut self, _symbol: SteelString) -> Self::Output {}

    fn visit_syntax_object(&mut self, syntax_object: Gc<Syntax>) -> Self::Output {
        if let Some(raw) = syntax_object.raw.clone() {
            self.push_back(raw);
        }

        self.push_back(syntax_object.syntax.clone());
    }

    fn visit_transducer(&mut self, transducer: Gc<Transducer>) -> Self::Output {
        for transducer in transducer.ops.iter() {
            match transducer.clone() {
                crate::values::transducers::Transducers::Map(m) => self.push_back(m),
                crate::values::transducers::Transducers::Filter(v) => self.push_back(v),
                crate::values::transducers::Transducers::Take(t) => self.push_back(t),
                crate::values::transducers::Transducers::Drop(d) => self.push_back(d),
                crate::values::transducers::Transducers::FlatMap(fm) => self.push_back(fm),
                crate::values::transducers::Transducers::Flatten => {}
                crate::values::transducers::Transducers::Window(w) => self.push_back(w),
                crate::values::transducers::Transducers::TakeWhile(tw) => self.push_back(tw),
                crate::values::transducers::Transducers::DropWhile(dw) => self.push_back(dw),
                crate::values::transducers::Transducers::Extend(e) => self.push_back(e),
                crate::values::transducers::Transducers::Cycle => {}
                crate::values::transducers::Transducers::Enumerating => {}
                crate::values::transducers::Transducers::Zipping(z) => self.push_back(z),
                crate::values::transducers::Transducers::Interleaving(i) => self.push_back(i),
                crate::values::transducers::Transducers::MapPair(i) => self.push_back(i),
            }
        }
    }

    fn visit_void(&mut self) -> Self::Output {}

    fn visit_pair(&mut self, pair: Gc<super::lists::Pair>) -> Self::Output {
        self.push_back(pair.car());
        self.push_back(pair.cdr());
    }
}

#[cfg(feature = "sync")]
impl<'a> BreadthFirstSearchSteelValReferenceVisitor2<'a> for MarkAndSweepContextRefQueue<'a> {
    type Output = ();

    fn default_output(&mut self) -> Self::Output {}

    fn pop_front(&mut self) -> Option<SteelValPointer> {
        self.local_queue.pop().or_else(|| self.queue.pop())
    }

    fn push_back(&mut self, value: &SteelVal) {
        self.stats.object_count += 1;

        if let Some(identity) = traced_identity(value) {
            self.reachable.insert(identity);
        }

        match value {
            SteelVal::BoxedFunction(function) => {
                if let Some(properties) = self.struct_types.function_properties(function) {
                    self.push_back(&properties);
                    self.save(properties);
                }
            }
            SteelVal::BoolV(_)
            | SteelVal::NumV(_)
            | SteelVal::IntV(_)
            | SteelVal::CharV(_)
            | SteelVal::Void
            | SteelVal::StringV(_)
            | SteelVal::FuncV(_)
            | SteelVal::SymbolV(_)
            | SteelVal::FutureFunc(_)
            | SteelVal::FutureV(_)
            | SteelVal::MutFunc(_)
            | SteelVal::BuiltIn(_)
            | SteelVal::ByteVector(_)
            | SteelVal::BigNum(_) => (),
            _ => {
                if let Some(p) = SteelValPointer::from_value(value) {
                    if self.local_queue.len() == self.local_queue.capacity() {
                        self.queue.push(p);
                    } else {
                        self.local_queue.push(p);
                    }
                }
            }
        }
    }

    // TODO: Revisit this when the boxed iterator is cleaned up
    fn visit_boxed_iterator(&mut self, iterator: &MutContainer<OpaqueIterator>) -> Self::Output {
        let guard = iterator.read();
        self.save(guard.root.clone());
        self.push_back(&guard.root);
    }

    fn visit_boxed_value(&mut self, boxed_value: &MutContainer<SteelVal>) -> Self::Output {
        let guard = boxed_value.read();
        self.save(guard.clone());
        self.push_back(&guard);
    }

    fn visit_closure(&mut self, closure: &ByteCodeLambda) -> Self::Output {
        for capture in closure.captures() {
            self.push_back(capture);
        }

        if let Some(contract) = closure.get_contract_information().as_ref() {
            self.push_back(contract);
        }
    }
    fn visit_continuation(
        &mut self,
        continuation: &MutContainer<ContinuationMark>,
    ) -> Self::Output {
        // TODO: Don't clone this here!
        let continuation = continuation.read();

        match &(*continuation) {
            ContinuationMark::Closed(continuation) => {
                self.reachable
                    .insert(continuation.current_frame.function.as_ptr() as usize);
                for value in &continuation.stack {
                    self.save(value.clone());
                    self.push_back(value);
                }

                for value in &continuation.current_frame.function.captures {
                    self.save(value.clone());
                    self.push_back(value);
                }

                for frame in &continuation.stack_frames {
                    self.reachable.insert(frame.function.as_ptr() as usize);
                    for value in &frame.function.captures {
                        self.save(value.clone());
                        self.push_back(value);
                    }

                    if let Some(handler) =
                        frame.attachments.as_ref().and_then(|x| x.handler.clone())
                    {
                        self.save(handler.clone());
                        self.push_back(&handler);
                    }
                }
            }

            ContinuationMark::Open(_) => {
                /*
                for value in &continuation.current_stack_values {
                    self.save(value.clone());
                    self.push_back(value);
                }

                for value in &continuation.current_frame.function.captures {
                    self.save(value.clone());
                    self.push_back(value);
                }
                */
            }
        }
    }
    // TODO: Come back to this?
    fn visit_custom_type(
        &mut self,
        custom_type: &'a MutContainer<Box<dyn CustomType>>,
    ) -> Self::Output {
        if !self.visited.insert(custom_type as *const _ as usize) {
            return;
        }
        let Some(custom) = read_custom_type(custom_type) else {
            return;
        };
        let properties = self
            .struct_types
            .descriptor_properties(custom.as_ref());
        if let Some(properties) = properties {
            self.push_back(&properties);
            self.save(properties);
        }
        let is_executor = custom.as_any_ref().is::<WillExecutor>();
        drop(custom);
        if is_executor {
            self.will_executors.push(custom_type);
        } else {
            self.visit_custom_children(custom_type);
        }
    }

    fn visit_hash_map(&mut self, hashmap: &super::HashMap<SteelVal, SteelVal>) -> Self::Output {
        if !self.visited.insert(hashmap as *const _ as usize) {
            return;
        }
        for (key, value) in hashmap.iter() {
            self.push_back(key);
            self.push_back(value);
        }
    }

    fn visit_hash_set(&mut self, hashset: &super::HashSet<SteelVal>) -> Self::Output {
        for value in hashset.iter() {
            self.push_back(value);
        }
    }

    fn visit_heap_allocated(&mut self, heap_ref: HeapRef<SteelVal>) -> Self::Output {
        if let Some(heap_ref) = heap_ref.inner.upgrade() {
            self.mark_heap_reference(&heap_ref);
        }
    }

    fn visit_immutable_vector(&mut self, vector: &Vector<SteelVal>) -> Self::Output {
        for value in vector.iter() {
            self.push_back(value);
        }
    }
    fn visit_list(&mut self, list: super::lists::CellPointer<SteelVal>) -> Self::Output {
        unsafe {
            super::lists::List::<SteelVal>::call_from_raw(list, |lst| {
                let mut node = lst.clone();
                loop {
                    for value in node.current_node_iter() {
                        self.push_back(value);
                    }
                    let Some(next) = node.next_ptr_as_usize() else {
                        break;
                    };
                    // tail can copy the next node, so record its original identity first.
                    self.reachable.insert(next);
                    node = node.tail(node.index()).unwrap();
                }
            })
        }
    }

    fn visit_mutable_vector(&mut self, vector: HeapRef<Vec<SteelVal>>) -> Self::Output {
        if let Some(vector) = vector.inner.upgrade() {
            self.mark_heap_vector(&vector);
        }
    }

    fn visit_reducer(&mut self, reducer: &Reducer) -> Self::Output {
        match reducer {
            Reducer::ForEach(f) => self.push_back(f),
            Reducer::Generic(rf) => {
                self.push_back(&rf.initial_value);
                self.push_back(&rf.function);
            }
            _ => {}
        }
    }

    fn visit_steel_struct(&mut self, steel_struct: &UserDefinedStruct) -> Self::Output {
        if let Some(properties) = self.struct_types.properties(steel_struct.type_descriptor) {
            self.push_back(&properties);
            self.save(properties);
        }
        for field in steel_struct.fields.iter() {
            self.push_back(field);
        }
    }

    fn visit_stream(&mut self, stream: &LazyStream) -> Self::Output {
        self.push_back(&stream.initial_value);
        self.push_back(&stream.stream_thunk);
    }

    fn visit_syntax_object(&mut self, syntax_object: &Syntax) -> Self::Output {
        if let Some(raw) = &syntax_object.raw {
            self.push_back(raw);
        }

        self.push_back(&syntax_object.syntax);
    }

    fn visit_transducer(&mut self, transducer: &Transducer) -> Self::Output {
        for transducer in transducer.ops.iter() {
            match &transducer {
                crate::values::transducers::Transducers::Map(m) => self.push_back(m),
                crate::values::transducers::Transducers::Filter(v) => self.push_back(v),
                crate::values::transducers::Transducers::Take(t) => self.push_back(t),
                crate::values::transducers::Transducers::Drop(d) => self.push_back(d),
                crate::values::transducers::Transducers::FlatMap(fm) => self.push_back(fm),
                crate::values::transducers::Transducers::Flatten => {}
                crate::values::transducers::Transducers::Window(w) => self.push_back(w),
                crate::values::transducers::Transducers::TakeWhile(tw) => self.push_back(tw),
                crate::values::transducers::Transducers::DropWhile(dw) => self.push_back(dw),
                crate::values::transducers::Transducers::Extend(e) => self.push_back(e),
                crate::values::transducers::Transducers::Cycle => {}
                crate::values::transducers::Transducers::Enumerating => {}
                crate::values::transducers::Transducers::Zipping(z) => self.push_back(z),
                crate::values::transducers::Transducers::Interleaving(i) => self.push_back(i),
                crate::values::transducers::Transducers::MapPair(i) => self.push_back(i),
            }
        }
    }

    fn visit_pair(&mut self, pair: &super::lists::Pair) -> Self::Output {
        self.push_back(pair.car_ref());
        self.push_back(pair.cdr_ref());
    }
}
