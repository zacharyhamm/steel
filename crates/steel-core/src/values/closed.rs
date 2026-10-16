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
    steel_vm::vm::{Continuation, ContinuationMark, Synchronizer, VmCore},
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
    structs::{UserDefinedStruct, VTable},
    transducers::{Reducer, Transducer},
};

#[cfg(feature = "sync")]
use super::lists::Pair;

#[cfg(feature = "sync")]
use super::Vector;

#[derive(Default)]
pub struct GlobalSlotRecycler {
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

    #[cfg(feature = "sync")]
    will_executors: Vec<GcMut<Box<dyn CustomType>>>,
}

impl GlobalSlotRecycler {
    pub fn free_shadowed_rooted_values(
        roots: &mut [SteelVal],
        symbol_map: &mut SymbolMap,
        heap: &mut Heap,
    ) {
        let mut recycler = GlobalSlotRecycler::default();

        recycler.recycle(roots, symbol_map, heap);
    }

    // TODO:
    // Take the global roots, without the shadowed values, and iterate over them,
    // push the values back, visit, mark visited, move on.
    pub fn recycle(&mut self, roots: &mut [SteelVal], symbol_map: &mut SymbolMap, heap: &mut Heap) {
        self.slots.clear();
        self.visited.clear();
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
        for properties in VTable::property_maps_snapshot() {
            self.push_back(SteelVal::HashMapV(properties.into()));
        }

        // Mark all unreachable for the purposes of the global
        // collection.
        heap.memory_free_list.mark_all_unreachable();
        heap.vector_free_list.mark_all_unreachable();

        // Actually walk the tree, looking for unreachable stuff
        self.visit();

        heap.memory_free_list.recount();
        heap.vector_free_list.recount();

        // TODO: Check this stuff!
        // put them back as unreachable

        // heap.memory.iter().for_each(|x| x.write().reset());
        // heap.vectors.iter().for_each(|x| x.write().reset());

        // Anything that is still remaining will require
        // getting added to the free list that is left.

        for index in self.slots.drain() {
            if index < roots.len() {
                symbol_map.free_list.free_list.push(index);
                roots[index] = SteelVal::Void;
            }
        }
    }
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

    let mut recycler = GlobalSlotRecycler::default();
    let mut symbol_map = SymbolMap::new();
    let mut heap = Heap::new();
    let mut roots = [receiver.clone(), SteelVal::Void];
    for pass in 1..=2 {
        roots[1] = SteelVal::IntV(42);
        symbol_map.free_list.shadowed_slots.push(1);
        recycler.recycle(&mut roots, &mut symbol_map, &mut heap);
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

impl BreadthFirstSearchSteelValVisitor for GlobalSlotRecycler {
    type Output = ();

    fn default_output(&mut self) -> Self::Output {}

    fn pop_front(&mut self) -> Option<SteelVal> {
        self.queue.pop()
    }

    fn visit(&mut self) -> Self::Output {
        use SteelVal::*;

        while let Some(value) = self.pop_front() {
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
            | SteelVal::BoxedFunction(_)
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
        self.push_back(boxed_value.read().clone());
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
                    self.slots.remove(&(instruction.payload_size.to_usize()));
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

        #[cfg(feature = "sync")]
        if custom_type.read().as_any_ref().is::<WillExecutor>() {
            self.will_executors.push(custom_type.clone());
        }

        let mut queue = MarkAndSweepContext {
            queue: &mut self.queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            teardown: false,
        };

        custom_type.read().visit_children(&mut queue);
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
        let mut queue = MarkAndSweepContext {
            queue: &mut self.queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            teardown: false,
        };

        if let Some(heap_ref) = heap_ref.inner.upgrade() {
            queue.mark_heap_reference(&heap_ref);
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
        let mut queue = MarkAndSweepContext {
            queue: &mut self.queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            teardown: false,
        };

        if let Some(vector) = vector.inner.upgrade() {
            queue.mark_heap_vector(&vector);
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

#[derive(Default)]
pub struct Roots {
    generation: usize,
    offset: usize,
    roots: rustc_hash::FxHashMap<(usize, usize), SteelVal>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct RootToken {
    generation: usize,
    offset: usize,
}

impl Drop for RootToken {
    fn drop(&mut self) {
        #[cfg(not(feature = "sync"))]
        let value = ROOTS.with(|x| x.borrow_mut().free(self));

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

    fn free(&mut self, token: &RootToken) -> Option<SteelVal> {
        self.roots.remove(&(token.generation, token.offset))
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
                WeakShared::weak_count(&heap_ref.inner) == 1
                    || !heap_ref.inner.upgrade().unwrap().read().is_reachable()
            }
            SteelVal::BoxedIterator(gc) => Gc::strong_count(gc) == 1,
            SteelVal::SyntaxObject(gc) => Gc::strong_count(gc) == 1,
            SteelVal::Boxed(gc) => Gc::strong_count(gc) == 1,
            SteelVal::HeapAllocated(heap_ref) => {
                WeakShared::weak_count(&heap_ref.inner) == 1
                    || !heap_ref.inner.upgrade().unwrap().read().is_reachable()
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
#[steel_derive::function(name = "will-register")]
pub fn will_register(
    will: SteelVal,
    value: SteelVal,
    func: SteelVal,
) -> Result<SteelVal, SteelErr> {
    let will = WillExecutor::as_ref(&will)?;
    will.register(value, func)?;
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
    fn struct_properties_remain_ordinary_will_roots() {
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
        let descriptor = match engine.extract_value("owner").unwrap() {
            SteelVal::CustomStruct(owner) => owner.type_descriptor,
            _ => panic!("expected a struct"),
        };
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
        assert_eq!(readiness(&engine, "executor"), [false]);

        crate::values::structs::VTable::set_entry(
            &descriptor,
            None,
            Gc::new(crate::values::HashMap::new()),
        );
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

    free_list.weak_collection();

    for var in &free_list.elements {
        assert!(!var.read().is_reachable());
    }
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
            teardown: true,
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

    free_list.weak_collection();

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

    free_list.weak_collection();

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

    struct Probe(#[allow(dead_code)] Arc<()>);
    impl Custom for Probe {}

    for vector in [false, true] {
        let count = Arc::new(());
        let mut heap = Heap::new();
        let child = Probe(count.clone()).into_steelval().unwrap();
        let root = if vector {
            SteelVal::MutableVector(heap.allocate_vec_without_collection(vec![child]))
        } else {
            SteelVal::HeapAllocated(heap.allocate_without_collection(child))
        };
        heap.memory_free_list.mark_all_unreachable();
        heap.vector_free_list.mark_all_unreachable();
        let queue = crossbeam_queue::SegQueue::new();
        let mut local_queue = Vec::new();
        let mut marker = MarkAndSweepContextRefQueue {
            queue: &queue,
            local_queue: &mut local_queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            will_executors: Vec::new(),
            reachable: rustc_hash::FxHashSet::default(),
        };
        match &root {
            SteelVal::HeapAllocated(value) => marker.visit_heap_allocated(value.clone()),
            SteelVal::MutableVector(value) => marker.visit_mutable_vector(value.clone()),
            _ => unreachable!(),
        }
        std::thread::spawn(move || drop(heap)).join().unwrap();
        #[cfg(feature = "biased")]
        steel_rc::QueueHandle::run_explicit_merge();
        assert_eq!(Arc::strong_count(&count), 2);
        // The queued child must outlive the heap, while expired heap references are skipped.
        marker.push_back(&root);
        marker.visit();
        drop(marker);
        assert_eq!(Arc::strong_count(&count), 1);
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
                let queue = crossbeam_queue::SegQueue::new();
                let mut local_queue = Vec::new();
                let mut ctx = MarkAndSweepContextRefQueue {
                    local_queue: &mut local_queue,
                    queue: &queue,
                    stats: MarkAndSweepStats::default(),
                    visited: rustc_hash::FxHashSet::default(),
                    will_executors: Vec::new(),
                    reachable: rustc_hash::FxHashSet::default(),
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

    // Update the counts for things
    fn recount(&mut self) {
        self.alloc_count = 0;
        for element in &mut self.elements {
            let guard = element.read();
            if !guard.is_reachable() {
                // Replace with an empty value... for now.
                // Want to keep the memory counts down.
                // let value = core::mem::replace(&mut guard.value, T::empty());
                self.alloc_count += 1;
            }
        }
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
    fn collect_on_condition(&mut self, func: fn(&HeapElement<T>) -> bool) -> usize {
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
                guard.value = T::empty();
            }
        });

        self.alloc_count += amount_dropped;
        log::debug!(target: "gc", "Free count after weak collection: {}", self.alloc_count);

        amount_dropped
    }

    // Full weak collection
    fn weak_collection(&mut self) -> usize {
        // Just mark them to be dead
        let res = self.collect_on_condition(|inner| StandardShared::weak_count(inner) == 0);
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

    fn strong_collection(&mut self) -> usize {
        self.collect_on_condition(|inner| !inner.read().is_reachable())
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

    // Update the counts for things
    fn recount(&mut self) {
        self.alloc_count = 0;
        for element in &mut self.elements {
            let guard = element.read();
            if !guard.is_reachable() {
                // Replace with an empty value... for now.
                // Want to keep the memory counts down.
                // let value = core::mem::replace(&mut guard.value, T::empty());
                self.alloc_count += 1;
            }
        }
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
    fn collect_on_condition(&mut self, func: fn(&HeapElement<T>) -> bool) -> usize {
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
                guard.value = T::empty();
            }
        });

        self.alloc_count += amount_dropped;
        log::debug!(target: "gc", "Free count after weak collection: {}", self.alloc_count);

        amount_dropped
    }

    // Full weak collection
    fn weak_collection(&mut self) -> usize {
        // Just mark them to be dead
        let res = self.collect_on_condition(|inner| StandardShared::weak_count(inner) == 0);
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

    fn strong_collection(&mut self) -> usize {
        self.collect_on_condition(|inner| !inner.read().is_reachable())
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
#[derive(Clone)]
pub struct Heap {
    count: usize,
    mark_and_sweep_queue: Vec<SteelVal>,

    maybe_memory_size: usize,

    skip_minor_collection: bool,
    memory_free_list: FreeList<SteelVal>,
    vector_free_list: FreeList<Vec<SteelVal>>,
}

#[cfg(feature = "sync")]
unsafe impl Send for Heap {}
#[cfg(feature = "sync")]
unsafe impl Sync for Heap {}

// Contiguous... no good? Perhaps a free list is actually better here?
// Can reuse the allocations more effectively, and can compact where needed.
struct MemorySpace {
    memory: Vec<HeapValue>,
    vectors: Vec<HeapVector>,
}

type MemoryBlock = (Vec<HeapValue>, Vec<HeapVector>);

impl Heap {
    pub(crate) fn trace_teardown_roots() -> (rustc_hash::FxHashSet<usize>, Vec<SteelVal>) {
        #[cfg(feature = "sync")]
        let mut roots: Vec<_> = GLOBAL_ROOTS
            .lock()
            .unwrap()
            .roots
            .values()
            .cloned()
            .collect();
        #[cfg(not(feature = "sync"))]
        let mut roots: Vec<_> = ROOTS
            .try_with(|roots| roots.borrow().roots.values().cloned().collect())
            .unwrap_or_default();
        roots.extend(
            VTable::property_maps_snapshot()
                .into_iter()
                .map(|map| SteelVal::HashMapV(map.into())),
        );
        let mut queue = Vec::new();
        let mut context = MarkAndSweepContext {
            queue: &mut queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            teardown: true,
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

    pub fn new() -> Self {
        Heap {
            count: 0,
            // mark_and_sweep_queue: VecDeque::with_capacity(256),
            mark_and_sweep_queue: Vec::with_capacity(256),

            maybe_memory_size: 0,

            skip_minor_collection: false,

            memory_free_list: FreeList::new(),
            vector_free_list: FreeList::new(),
        }
    }

    pub fn new_empty() -> Self {
        Heap {
            count: 0,
            mark_and_sweep_queue: Vec::new(),
            maybe_memory_size: 0,
            skip_minor_collection: false,
            memory_free_list: FreeList::new(),
            vector_free_list: FreeList::new(),
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
            self.memory_free_list.weak_collection();

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
            self.vector_free_list.weak_collection();

            if self.vector_free_list.percent_full() > 0.30 {
                self.vector_free_list.should_run_weak = false;
            }
        }

        if self.vector_free_list.percent_full() > 0.95 || force {
            // let now = crate::time::Instant::now();
            // Attempt a weak collection
            log::debug!(target: "gc", "Vec<SteelVal> gc invocation");
            self.vector_free_list.weak_collection();
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
            self.vector_free_list.weak_collection();

            if self.vector_free_list.percent_full() > 0.30 {
                self.vector_free_list.should_run_weak = false;
            }
        }

        if self.vector_free_list.percent_full() > 0.95 {
            // let now = crate::time::Instant::now();
            // Attempt a weak collection
            log::debug!(target: "gc", "Vec<SteelVal> gc invocation");
            self.vector_free_list.weak_collection();
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
        let stats = self.mark(
            root_value,
            root_vector,
            roots,
            function_stack,
            globals,
            constants,
            tls,
            synchronizer,
        );

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

        let mut context = MarkAndSweepContext {
            queue: &mut self.mark_and_sweep_queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            teardown: false,
        };

        // Pause all threads
        synchronizer.stop_threads();
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
        for properties in VTable::property_maps_snapshot() {
            context.push_back(SteelVal::HashMapV(properties.into()));
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

        #[cfg(feature = "sync")]
        {
            GLOBAL_ROOTS
                .lock()
                .unwrap()
                .roots
                .values()
                .for_each(|value| context.push_back(value.clone()))
        }

        #[cfg(not(feature = "sync"))]
        {
            ROOTS.with(|x| {
                x.borrow()
                    .roots
                    .values()
                    .for_each(|value| context.push_back(value.clone()))
            });
        }

        // Each confined interpreter has its own memory budget. Mark on its current
        // thread instead of allocating a machine-sized worker pool at the first GC.
        #[cfg(feature = "sync")]
        let stats = {
            let queue = crossbeam_queue::SegQueue::new();
            let mut local_queue = Vec::with_capacity(4096);
            let mut marker = MarkAndSweepContextRefQueue {
                queue: &queue,
                local_queue: &mut local_queue,
                stats: MarkAndSweepStats::default(),
                visited: rustc_hash::FxHashSet::default(),
                will_executors: Vec::new(),
                reachable,
            };
            for value in context.queue.iter() {
                marker.push_back(value);
            }
            marker.visit();
            marker.retain_wills();
            context.queue.clear();
            marker.stats
        };
        #[cfg(not(feature = "sync"))]
        let stats = {
            context.visit();
            context.stats
        };
        // Free slots must release their payloads even if no later allocation reuses them.
        self.memory_free_list.strong_collection();
        self.vector_free_list.strong_collection();
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
    teardown: bool,
}

impl<'a> MarkAndSweepContext<'a> {
    pub(crate) fn mark_heap_reference(
        &mut self,
        heap_ref: &StandardSharedMut<HeapAllocated<SteelVal>>,
    ) {
        if !self.teardown {
            let mut guard = heap_ref.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
        }

        self.stats.memory_reached_count += 1;

        self.push_back(heap_ref.read().value.clone());
    }

    // Visit the heap vector, mark it as visited!
    pub(crate) fn mark_heap_vector(
        &mut self,
        heap_vector: &StandardSharedMut<HeapAllocated<Vec<SteelVal>>>,
    ) {
        if !self.teardown {
            let mut guard = heap_vector.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
        }

        self.stats.vector_reached_count += 1;

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
}

impl core::ops::Add for MarkAndSweepStats {
    type Output = MarkAndSweepStats;

    fn add(mut self, rhs: Self) -> Self::Output {
        self.object_count += rhs.object_count;
        self.memory_reached_count += rhs.memory_reached_count;
        self.vector_reached_count += rhs.vector_reached_count;
        self
    }
}

#[cfg(feature = "sync")]
pub struct MarkAndSweepContextRefQueue<'a> {
    // Thread local queue + larger queue when it runs out?
    // Try to push on to local queue first.
    local_queue: &'a mut Vec<SteelValPointer>,
    queue: &'a crossbeam_queue::SegQueue<SteelValPointer>,
    stats: MarkAndSweepStats,
    visited: rustc_hash::FxHashSet<usize>,
    will_executors: Vec<&'a MutContainer<Box<dyn CustomType>>>,
    reachable: rustc_hash::FxHashSet<usize>,
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
                    pending.ready |= traced_identity(pending.pair.car_ref()).map_or_else(
                        || pending.is_unreachable(),
                        |identity| !reachable.contains(&identity),
                    );
                }
            }
            for index in processed..end {
                let custom = self.will_executors[index];
                self.visit_custom_children(custom);
            }
            self.visit();
            processed = end;
        }
    }

    fn visit_custom_children(&mut self, custom_type: &MutContainer<Box<dyn CustomType>>) {
        let mut queue = Vec::new();
        let mut temporary_queue = MarkAndSweepContext {
            queue: &mut queue,
            stats: MarkAndSweepStats::default(),
            visited: rustc_hash::FxHashSet::default(),
            teardown: false,
        };

        custom_type.read().visit_children(&mut temporary_queue);

        self.stats.memory_reached_count += temporary_queue.stats.memory_reached_count;
        self.stats.object_count += temporary_queue.stats.object_count;
        self.stats.vector_reached_count += temporary_queue.stats.vector_reached_count;

        for value in queue {
            self.push_back(&value);
            self.save(value);
        }
    }

    pub(crate) fn mark_heap_reference(
        &mut self,
        heap_ref: &StandardSharedMut<HeapAllocated<SteelVal>>,
    ) {
        {
            let mut guard = heap_ref.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
        }

        self.stats.memory_reached_count += 1;

        let guard = heap_ref.read();
        self.save(guard.value.clone());
        self.push_back(&guard.value);
    }

    // Visit the heap vector, mark it as visited!
    pub(crate) fn mark_heap_vector(
        &mut self,
        heap_vector: &StandardSharedMut<HeapAllocated<Vec<SteelVal>>>,
    ) {
        {
            let mut guard = heap_vector.write();
            if guard.is_reachable() {
                return;
            }
            guard.mark_reachable();
        }

        self.stats.vector_reached_count += 1;

        for value in heap_vector.read().value.iter() {
            self.save(value.clone());
            self.push_back(value);
        }
    }

    pub(crate) fn save(&mut self, value: SteelVal) {
        self.stats.keep_alive.push(value);
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
        if self.teardown {
            // List slices can share an address while exposing different elements.
            if !matches!(value, SteelVal::ListV(_)) {
                if let Some(identity) = traced_identity(&value) {
                    if !self.visited.insert(identity) {
                        return;
                    }
                    self.stats.keep_alive.push(value.clone());
                }
            }
        }
        self.stats.object_count += 1;

        // TODO: Determine if all numbers should push back.
        match &value {
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
            | SteelVal::BoxedFunction(_)
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
        if !self.teardown && !self.visited.insert(custom_type.as_ptr() as usize) {
            return;
        }
        custom_type.read().visit_children(self);
    }

    fn visit_float(&mut self, _float: f64) -> Self::Output {}

    fn visit_function_pointer(&mut self, _ptr: FunctionSignature) -> Self::Output {}

    fn visit_future(&mut self, _future: Gc<FutureResult>) -> Self::Output {}

    fn visit_future_function(&mut self, _function: BoxedAsyncFunctionSignature) -> Self::Output {}

    fn visit_hash_map(&mut self, hashmap: SteelHashMap) -> Self::Output {
        if !self.teardown && !self.visited.insert(hashmap.0.as_ptr() as usize) {
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

    fn visit_list(&mut self, list: List<SteelVal>) -> Self::Output {
        for value in list {
            self.push_back(value);
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
            | SteelVal::BoxedFunction(_)
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
        if custom_type.read().as_any_ref().is::<WillExecutor>() {
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
