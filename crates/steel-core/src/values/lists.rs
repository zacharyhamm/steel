use core::cell::Cell;
use core::hash::{Hash, Hasher};

use im_lists::{
    handler::{DefaultDropHandler, DropHandler},
    shared::PointerFamily,
};

use crate::{
    gc::Gc,
    rvals::{FromSteelVal, IntoSteelVal},
    SteelVal,
};

// TODO:
// Builtin immutable pairs
#[derive(Clone)]
pub struct Pair {
    pub(crate) car: SteelVal,
    pub(crate) cdr: SteelVal,
}

impl Pair {
    pub fn cons(car: SteelVal, cdr: SteelVal) -> Self {
        Pair { car, cdr }
    }

    pub fn car(&self) -> SteelVal {
        self.car.clone()
    }

    pub fn cdr(&self) -> SteelVal {
        self.cdr.clone()
    }

    pub fn car_ref(&self) -> &SteelVal {
        &self.car
    }

    pub fn cdr_ref(&self) -> &SteelVal {
        &self.cdr
    }
}

impl Hash for Pair {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Follow cdr chains in place; only a pair in car position defers its cdr.
        let mut pending = Vec::new();
        let mut pair = self;
        loop {
            if let SteelVal::Pair(car) = &pair.car {
                core::mem::discriminant(&pair.car).hash(state);
                pending.push(&pair.cdr);
                pair = car;
                continue;
            }
            pair.car.hash(state);
            let mut next = &pair.cdr;
            loop {
                if let SteelVal::Pair(cdr) = next {
                    core::mem::discriminant(next).hash(state);
                    pair = cdr;
                    break;
                }
                next.hash(state);
                match pending.pop() {
                    Some(value) => next = value,
                    None => return,
                }
            }
        }
    }
}

impl From<Pair> for SteelVal {
    fn from(pair: Pair) -> Self {
        SteelVal::Pair(Gc::new(pair))
    }
}

impl core::fmt::Debug for Pair {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "({} . {})", &self.car, &self.cdr)
    }
}

#[cfg(feature = "without-drop-protection")]
type DropHandlerChoice = im_lists::handler::DefaultDropHandler;
#[cfg(not(feature = "without-drop-protection"))]
type DropHandlerChoice = list_drop_handler::ListDropHandler;

thread_local! {
    pub static DEPTH: Cell<usize> = const { Cell::new(0) };
}

pub struct GcPointerType;

impl PointerFamily for GcPointerType {
    type Pointer<T: 'static> = Gc<T>;

    // Every list node and empty list a thread creates starts here, so the storage probe is
    // installed before that thread's own lists are dropped.
    fn new<T: 'static>(value: T) -> Self::Pointer<T> {
        probe_list_storage();
        Gc::new(value)
    }

    fn strong_count<T: 'static>(this: &Self::Pointer<T>) -> usize {
        Gc::strong_count(this)
    }

    fn try_unwrap<T: 'static>(this: Self::Pointer<T>) -> Option<T> {
        Gc::try_unwrap(this).ok()
    }

    fn get_mut<T: 'static>(this: &mut Self::Pointer<T>) -> Option<&mut T> {
        Gc::get_mut(this)
    }

    fn ptr_eq<T: 'static>(this: &Self::Pointer<T>, other: &Self::Pointer<T>) -> bool {
        Gc::ptr_eq(this, other)
    }

    fn make_mut<T: Clone + 'static>(ptr: &mut Self::Pointer<T>) -> &mut T {
        Gc::make_mut(ptr)
    }

    fn clone<T: 'static>(ptr: &Self::Pointer<T>) -> Self::Pointer<T> {
        Gc::clone(ptr)
    }

    fn as_ptr<T: 'static>(this: &Self::Pointer<T>) -> *const T {
        Gc::as_ptr(this)
    }

    fn into_raw<T: 'static>(this: Self::Pointer<T>) -> *const T {
        Gc::into_raw(this)
    }

    unsafe fn from_raw<T: 'static>(this: *const T) -> Self::Pointer<T> {
        Gc::from_raw(this)
    }
}

// Draining a list builds an empty list through im-lists' thread-local map, and thread-local
// destructors run in an unspecified order. A thread-local that still owns lists can be
// destroyed after that map, so drops track whether it is gone. A const `Cell` registers no
// destructor, so this state stays readable while other thread-locals are torn down.
const LIST_STORAGE_UNPROBED: u8 = 0;
const LIST_STORAGE_ALIVE: u8 = 1;
const LIST_STORAGE_DESTROYED: u8 = 2;

thread_local! {
    static LIST_STORAGE: Cell<u8> = const { Cell::new(LIST_STORAGE_UNPROBED) };
}

// im-lists keeps one map of empty lists per thread, keyed by list type. The probe's empty
// list lives in that map, and the map holds its last reference, so releasing that reference
// means the map is being destroyed.
struct StorageProbe;

// The `Option` lets the consuming operations move the pointer out of a type with `Drop`.
struct ProbePointer<T>(Option<alloc::rc::Rc<T>>);

impl<T> ProbePointer<T> {
    fn rc(&self) -> &alloc::rc::Rc<T> {
        self.0.as_ref().unwrap()
    }
}

impl<T> core::ops::Deref for ProbePointer<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.rc()
    }
}

impl<T> Drop for ProbePointer<T> {
    fn drop(&mut self) {
        if self
            .0
            .as_ref()
            .is_some_and(|rc| alloc::rc::Rc::strong_count(rc) == 1)
        {
            LIST_STORAGE.set(LIST_STORAGE_DESTROYED);
        }
    }
}

impl PointerFamily for StorageProbe {
    type Pointer<T: 'static> = ProbePointer<T>;

    fn new<T: 'static>(value: T) -> Self::Pointer<T> {
        ProbePointer(Some(alloc::rc::Rc::new(value)))
    }

    fn strong_count<T: 'static>(this: &Self::Pointer<T>) -> usize {
        alloc::rc::Rc::strong_count(this.rc())
    }

    fn try_unwrap<T: 'static>(mut this: Self::Pointer<T>) -> Option<T> {
        alloc::rc::Rc::try_unwrap(this.0.take()?).ok()
    }

    fn get_mut<T: 'static>(this: &mut Self::Pointer<T>) -> Option<&mut T> {
        alloc::rc::Rc::get_mut(this.0.as_mut()?)
    }

    fn ptr_eq<T: 'static>(this: &Self::Pointer<T>, other: &Self::Pointer<T>) -> bool {
        alloc::rc::Rc::ptr_eq(this.rc(), other.rc())
    }

    fn make_mut<T: Clone + 'static>(ptr: &mut Self::Pointer<T>) -> &mut T {
        alloc::rc::Rc::make_mut(ptr.0.as_mut().unwrap())
    }

    fn clone<T: 'static>(ptr: &Self::Pointer<T>) -> Self::Pointer<T> {
        ProbePointer(ptr.0.clone())
    }

    fn as_ptr<T: 'static>(this: &Self::Pointer<T>) -> *const T {
        alloc::rc::Rc::as_ptr(this.rc())
    }

    fn into_raw<T: 'static>(mut this: Self::Pointer<T>) -> *const T {
        alloc::rc::Rc::into_raw(this.0.take().unwrap())
    }

    unsafe fn from_raw<T: 'static>(this: *const T) -> Self::Pointer<T> {
        ProbePointer(Some(unsafe { alloc::rc::Rc::from_raw(this) }))
    }
}

// The map supports reentrant use from an empty list's initializer, which is where the first
// `GcPointerType::new` on a thread usually comes from.
fn probe_list_storage() {
    if LIST_STORAGE.get() == LIST_STORAGE_UNPROBED {
        LIST_STORAGE.set(LIST_STORAGE_ALIVE);
        drop(im_lists::list::GenericList::<
            (),
            StorageProbe,
            4,
            2,
            DefaultDropHandler,
        >::new());
    }
}

pub(crate) fn list_storage_destroyed() -> bool {
    LIST_STORAGE.get() == LIST_STORAGE_DESTROYED
}

/// Take a list's elements without im-lists' thread-local storage, leaving it empty.
///
/// The elements are cloned out before the nodes are released, so releasing the nodes only
/// decrements each element. The old node is dropped as a bare pointer, which does not run
/// the list's drop handler again, and its own drop walks the next nodes iteratively.
pub(crate) fn copy_out(list: &mut List<SteelVal>) -> Vec<SteelVal> {
    let elements = list.iter().cloned().collect();
    let empty = List::new_with_capacity();
    drop(core::mem::replace(
        list.inner_ptr_mut(),
        empty.inner_ptr().clone(),
    ));
    elements
}

#[cfg(not(feature = "without-drop-protection"))]
mod list_drop_handler {

    use std::collections::VecDeque;

    use super::*;

    pub struct ListDropHandler;

    use crate::rvals::cycles::{
        drop_impls::{drops_shallowly, DROP_BUFFER},
        IterativeDropHandler,
    };

    fn drain(obj: &mut List<SteelVal>, drop_buffer: &mut VecDeque<SteelVal>) {
        for value in core::mem::take(obj).draining_iterator() {
            if !drops_shallowly(&value) {
                drop_buffer.push_back(value);
            }
        }

        IterativeDropHandler::bfs(drop_buffer);
    }

    impl DropHandler<im_lists::list::GenericList<SteelVal, PointerType, 4, 2, Self>>
        for ListDropHandler
    {
        #[inline(always)]
        fn drop_handler(obj: &mut im_lists::list::GenericList<SteelVal, PointerType, 4, 2, Self>) {
            if obj.is_empty() || obj.strong_count() != 1 {
                return;
            }

            // Only thread-local teardown reaches this, so it does not use the drop buffer.
            if list_storage_destroyed() {
                let mut buffer: VecDeque<_> = copy_out(obj)
                    .into_iter()
                    .filter(|value| !drops_shallowly(value))
                    .collect();
                IterativeDropHandler::bfs(&mut buffer);
                return;
            }

            let drained = DROP_BUFFER.try_with(|drop_buffer| match drop_buffer.try_borrow_mut() {
                Ok(mut drop_buffer) => drain(obj, &mut drop_buffer),
                Err(_) => drain(obj, &mut VecDeque::new()),
            });

            if drained.is_err() {
                drain(obj, &mut VecDeque::new());
            }
        }
    }
}

type PointerType = GcPointerType;

pub type SteelList<T> = im_lists::list::GenericList<T, PointerType, 4, 2, DefaultDropHandler>;

pub type List<T> = im_lists::list::GenericList<T, PointerType, 4, 2, DropHandlerChoice>;

pub(crate) type CellPointer<T> = im_lists::list::RawCell<T, PointerType, 4, 2, DropHandlerChoice>;

pub type ConsumingIterator<T> =
    im_lists::list::ConsumingIter<T, PointerType, 4, 2, DropHandlerChoice>;

impl<T: FromSteelVal + Clone, D: im_lists::handler::DropHandler<Self>> FromSteelVal
    for im_lists::list::GenericList<T, PointerType, 4, 2, D>
{
    fn from_steelval(val: &SteelVal) -> crate::rvals::Result<Self> {
        if let SteelVal::ListV(l) = val {
            l.iter().map(T::from_steelval).collect()
        } else {
            stop!(TypeMismatch => "Unable to convert SteelVal to List, found: {}", val);
        }
    }
}

impl<T: IntoSteelVal + Clone, D: im_lists::handler::DropHandler<Self>> IntoSteelVal
    for im_lists::list::GenericList<T, PointerType, 4, 2, D>
{
    fn into_steelval(self) -> crate::rvals::Result<SteelVal> {
        self.into_iter()
            .map(|x| x.into_steelval())
            .collect::<crate::rvals::Result<List<_>>>()
            .map(SteelVal::ListV)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    #[cfg(not(feature = "without-drop-protection"))]
    #[test]
    fn deep_pair_trees_hash_and_drop_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                #[cfg(all(feature = "sync", feature = "biased"))]
                steel_rc::register_thread();
                thread_local! {
                    static LAST_PAIR: std::cell::RefCell<Option<SteelVal>> = const {
                        std::cell::RefCell::new(None)
                    };
                }
                // Initialize before DROP_BUFFER so this pair is destroyed after that TLS is gone.
                LAST_PAIR.with(|pair| assert!(pair.borrow().is_none()));
                for shape in 0..3 {
                    let mut value = SteelVal::IntV(0);
                    for depth in 0..30_000 {
                        value = if shape == 0 || (shape == 2 && depth % 2 == 0) {
                            Pair::cons(value, SteelVal::IntV(1)).into()
                        } else {
                            Pair::cons(SteelVal::IntV(1), value).into()
                        };
                    }
                    value.hash(&mut DefaultHasher::new());
                    if shape == 0 {
                        drop(value);
                    } else if shape == 1 {
                        crate::rvals::cycles::drop_impls::DROP_BUFFER.with(|buffer| {
                            let _borrow = buffer.borrow_mut();
                            drop(value);
                        });
                    } else {
                        LAST_PAIR.with(|pair| *pair.borrow_mut() = Some(value));
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn pair_hash_preserves_recursive_field_order() {
        fn hash_recursively(value: &SteelVal, state: &mut impl Hasher) {
            if let SteelVal::Pair(pair) = value {
                core::mem::discriminant(value).hash(state);
                hash_recursively(pair.car_ref(), state);
                hash_recursively(pair.cdr_ref(), state);
            } else {
                value.hash(state);
            }
        }

        let inner: SteelVal = Pair::cons(SteelVal::IntV(1), SteelVal::BoolV(false)).into();
        for tail in [
            SteelVal::IntV(2),
            inner.clone(),
            SteelVal::ListV(Default::default()),
        ] {
            let value: SteelVal = Pair::cons(inner.clone(), tail).into();
            let mut expected = DefaultHasher::new();
            hash_recursively(&value, &mut expected);
            let mut actual = DefaultHasher::new();
            value.hash(&mut actual);
            assert_eq!(actual.finish(), expected.finish());
        }
    }
}
