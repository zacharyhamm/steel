use std::alloc::Layout;
use std::any::Any;
use std::borrow::Borrow;
use std::convert::Infallible;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::Deref;
use std::pin::Pin;
use std::ptr::{drop_in_place, NonNull};
use std::sync::atomic::{AtomicU32, AtomicUsize};
use std::sync::LazyLock;
use std::thread::JoinHandle;
use std::{cell::Cell, sync::atomic::Ordering};

use core::num::NonZeroUsize;

use std::{alloc, cmp, fmt, iter, mem, ptr};

use std::hash::{Hash, Hasher};

thread_local! {
    static OWNER: ThreadOwner = ThreadOwner::new();
    // No TLS destructor: retired releases must also work after other thread-locals are gone.
    static RETIRED: Cell<Option<ManuallyDrop<Vec<Wrapper>>>> = const { Cell::new(None) };
}

static NEXT_THREAD_ID: AtomicUsize = AtomicUsize::new(1);

/// An allocation's owner identity is never reused, even after its thread exits.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct ThreadId(NonZeroUsize);

impl ThreadId {
    #[inline]
    fn current_thread() -> Option<Self> {
        OWNER.try_with(|owner| owner.id).ok()
    }
}

struct ThreadOwner {
    id: ThreadId,
}

impl ThreadOwner {
    fn new() -> Self {
        let mut id = NEXT_THREAD_ID.load(Ordering::Relaxed);
        loop {
            let next = id.checked_add(1).unwrap_or_else(|| std::process::abort());
            match NEXT_THREAD_ID.compare_exchange_weak(
                id,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(current) => id = current,
            }
        }
        let id = ThreadId(NonZeroUsize::new(id).unwrap());
        QUEUE.map.insert(id, Vec::new());
        Self { id }
    }
}

impl Drop for ThreadOwner {
    fn drop(&mut self) {
        // Removal synchronizes the final local counts with releases after retirement.
        let pending = QUEUE.map.remove(&self.id);
        drop(pending);
    }
}

#[repr(C)]
pub struct RcWord {
    // Immutable owner identity; FLAG_MERGED publishes the transition to shared counting.
    thread_id: AtomicUsize,
    biased_counter: Cell<u32>,
    shared: SharedPacked,
}

pub struct SharedPacked(AtomicU32);

impl SharedPacked {
    #[inline]
    pub fn load(&self, order: Ordering) -> Packed {
        Packed(self.0.load(order))
    }

    #[inline]
    pub fn compare_exchange(
        &self,
        current: Packed,
        new: Packed,
        success: Ordering,
        failure: Ordering,
    ) -> Result<u32, u32> {
        self.0.compare_exchange(current.0, new.0, success, failure)
    }
}

pub const FLAG_MERGED: u32 = 1 << 31;
pub const FLAG_QUEUED: u32 = 1 << 30;

const VALUE_BITS: u32 = 30;
const VALUE_MASK: u32 = (1 << VALUE_BITS) - 1;
const VALUE_SIGN_BIT: u32 = 1 << (VALUE_BITS - 1);

#[derive(Copy, Clone, PartialEq, PartialOrd, Debug)]
pub struct Packed(u32);

impl Packed {
    pub fn set_queued(&mut self, queued: bool) {
        let mask = FLAG_QUEUED;
        if queued {
            self.0 |= mask;
        } else {
            self.0 &= !mask
        }
    }

    pub fn set_merged(&mut self, merged: bool) {
        let mask = FLAG_MERGED;
        if merged {
            self.0 |= mask
        } else {
            self.0 &= !mask
        }
    }

    pub fn get_merged(&self) -> bool {
        self.is_merged()
    }

    pub fn get_queued(&self) -> bool {
        self.is_queued()
    }

    pub fn is_merged(&self) -> bool {
        self.0 & FLAG_MERGED != 0
    }

    pub fn is_queued(&self) -> bool {
        self.0 & FLAG_QUEUED != 0
    }

    // pub fn value(&self) -> i32 {
    //     (self.0 & VALUE_MASK) as _
    // }

    pub fn get_counter(&self) -> i32 {
        self.value()
    }

    // fn set_value(&mut self, value: i32) {
    //     assert!(value >= -(1 << 29) && value < (1 << 29));
    //     let v = (value as u32) & VALUE_MASK;
    //     // self.0 = (self.0 & !VALUE_MASK) | v;

    //     self.0 = v;
    // }

    fn value(&self) -> i32 {
        let raw = self.0 & VALUE_MASK;

        if raw & VALUE_SIGN_BIT != 0 {
            // Sign-extend from bit 29
            (raw | !VALUE_MASK) as i32
        } else {
            raw as i32
        }
    }

    pub fn set_counter(&mut self, value: i32) {
        self.set_value(value);
    }

    fn set_value(&mut self, value: i32) {
        assert!(value >= -(1 << 29) && value < (1 << 29));
        let v = (value as u32) & VALUE_MASK;
        self.0 = (self.0 & !VALUE_MASK) | v;
    }

    fn update_counter(&mut self, f: impl FnOnce(i32) -> i32) {
        self.set_value((f)(self.value()))
    }

    fn new_with(value: i32, merged: bool, queued: bool) -> Self {
        // Ensure value fits in signed 30 bits
        assert!(value >= -(1 << 29) && value < (1 << 29));

        let mut bits = (value as u32) & VALUE_MASK;

        if merged {
            bits |= FLAG_MERGED;
        }
        if queued {
            bits |= FLAG_QUEUED;
        }

        Self(bits)
    }

    pub fn new() -> Self {
        Self::new_with(0, false, false)
    }
}

#[test]
fn packed_vs_unpacked() {
    let mut packed = Packed::new();

    packed.set_merged(true);

    assert_eq!(packed.get_merged(), true);
    assert_eq!(packed.get_queued(), false);
    assert_eq!(packed.get_counter(), 0);

    packed.set_merged(false);
    assert_eq!(packed.get_merged(), false);
    assert_eq!(packed.get_queued(), false);
    assert_eq!(packed.get_counter(), 0);

    packed.set_value(100);
    assert_eq!(packed.get_merged(), false);
    assert_eq!(packed.get_queued(), false);
    assert_eq!(packed.get_counter(), 100);

    packed.set_value(-1);
    assert_eq!(packed.get_merged(), false);
    assert_eq!(packed.get_queued(), false);
    assert_eq!(packed.get_counter(), -1);

    packed.set_value(-100);
    packed.set_queued(true);
    assert_eq!(packed.get_merged(), false);
    assert_eq!(packed.get_queued(), true);
    assert_eq!(packed.get_counter(), -100);
}

impl SharedPacked {
    pub fn set_flag_queued(&self, queued: bool) {
        let mask = FLAG_QUEUED;
        if queued {
            self.0.fetch_or(mask, Ordering::Relaxed);
        } else {
            self.0.fetch_and(!mask, Ordering::Relaxed);
        }
    }

    pub fn set_flag_merged(&self, merged: bool) {
        let mask = FLAG_MERGED;
        if merged {
            self.0.fetch_or(mask, Ordering::Relaxed);
        } else {
            self.0.fetch_and(!mask, Ordering::Relaxed);
        }
    }

    pub fn is_merged(&self) -> bool {
        self.0.load(Ordering::Relaxed) & FLAG_MERGED != 0
    }

    pub fn is_queued(&self) -> bool {
        self.0.load(Ordering::Relaxed) & FLAG_QUEUED != 0
    }

    pub fn value(&self) -> u32 {
        self.0.load(Ordering::Relaxed) & VALUE_MASK
    }
}

#[repr(C)]
pub struct RcBox<T: ?Sized> {
    rcword: RcWord,
    data: T,
}

impl RcWord {
    pub fn new() -> Self {
        let owner = ThreadId::current_thread();
        Self {
            thread_id: AtomicUsize::new(owner.map_or(0, |id| id.0.get())),
            biased_counter: Cell::new(u32::from(owner.is_some())),
            // TLS destructors can allocate after OWNER has already been destroyed.
            shared: SharedPacked(AtomicU32::new(
                Packed::new_with(i32::from(owner.is_none()), owner.is_none(), false).0,
            )),
        }
    }

    fn is_owner(&self) -> bool {
        ThreadId::current_thread()
            .is_some_and(|id| self.thread_id.load(Ordering::Relaxed) == id.0.get())
            && !self.shared.load(Ordering::Acquire).is_merged()
    }

    // Only the owner, or a releaser synchronized with its retirement, may merge.
    fn merge_counts(&self, release_queue: bool) -> DecrementAction {
        let mut old = self.shared.load(Ordering::Acquire);
        let local = if old.is_merged() {
            0
        } else {
            self.biased_counter.get() as i32
        };
        loop {
            let mut new = old;
            if !old.is_merged() {
                new.update_counter(|count| count + local);
                new.set_merged(true);
            }
            if release_queue {
                new.set_queued(false);
            }
            match self
                .shared
                .compare_exchange(old, new, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => {
                    // Do not touch metadata after publishing: another release can free it.
                    return if new.get_counter() == 0 && !new.is_queued() {
                        DecrementAction::Deallocate
                    } else {
                        DecrementAction::DoNothing
                    };
                }
                Err(current) => old = Packed(current),
            }
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum DecrementAction {
    DoNothing,
    Queue,
    Deallocate,
}

impl<T: ?Sized> RcBox<T> {
    pub fn increment(&self) {
        if self.rcword.is_owner() {
            self.fast_increment();
        } else {
            self.slow_increment();
        }
    }

    pub fn fast_increment(&self) {
        let counter = self.rcword.biased_counter.get();
        if counter >= (1 << 29) - 1 {
            std::process::abort();
        }
        self.rcword.biased_counter.set(counter + 1);
    }

    pub fn slow_increment(&self) {
        let mut old = self.rcword.shared.load(Ordering::Relaxed);
        loop {
            let mut new = old;
            new.update_counter(|count| count + 1);
            match self.rcword.shared.compare_exchange(
                old,
                new,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(current) => old = Packed(current),
            }
        }
    }

    pub fn decrement(&self) -> DecrementAction {
        if self.rcword.is_owner() {
            self.fast_decrement()
        } else {
            self.slow_decrement()
        }
    }

    pub fn fast_decrement(&self) -> DecrementAction {
        let count = self.rcword.biased_counter.get() - 1;
        self.rcword.biased_counter.set(count);
        if count > 0 {
            DecrementAction::DoNothing
        } else {
            self.rcword.merge_counts(false)
        }
    }

    pub fn slow_decrement(&self) -> DecrementAction {
        let mut old = self.rcword.shared.load(Ordering::Relaxed);
        loop {
            let mut new = old;
            new.update_counter(|count| count - 1);
            if new.get_counter() < 0 && !new.is_merged() {
                // The queued bit retains the allocation through enqueue and merging.
                new.set_queued(true);
            }
            match self
                .rcword
                .shared
                .compare_exchange(old, new, Ordering::AcqRel, Ordering::Relaxed)
            {
                Ok(_) => {
                    return if !old.is_queued() && new.is_queued() {
                        DecrementAction::Queue
                    } else if new.is_merged() && !new.is_queued() && new.get_counter() == 0 {
                        DecrementAction::Deallocate
                    } else {
                        DecrementAction::DoNothing
                    };
                }
                Err(current) => old = Packed(current),
            }
        }
    }

    fn has_unique_ref(&self) -> bool {
        let meta = &self.rcword;
        let word = meta.shared.load(Ordering::Acquire);
        if word.is_queued() {
            return false;
        }
        if word.is_merged() {
            word.get_counter() == 1
        } else {
            meta.is_owner() && meta.biased_counter.get() == 1 && word.get_counter() == 0
        }
    }
}

pub struct Wrapper(Box<ManuallyDrop<dyn BiasedMerge>>);

// Foreign releases can only originate from values whose payload may cross threads.
unsafe impl Send for Wrapper {}
unsafe impl Sync for Wrapper {}

impl Drop for Wrapper {
    fn drop(&mut self) {
        if self.0.meta_outer().merge_counts(true) == DecrementAction::Deallocate {
            unsafe { self.0.drop_contents_and_maybe_box_outer() };
        }
    }
}

struct RetiredDrain;

impl RetiredDrain {
    fn enqueue(value: Wrapper) {
        let active = RETIRED.with(|slot| {
            let pending = slot.take();
            let active = pending.is_some();
            let mut values = pending.map(ManuallyDrop::into_inner).unwrap_or_default();
            values.push(value);
            slot.set(Some(ManuallyDrop::new(values)));
            active
        });
        if !active {
            let guard = Self;
            guard.drain();
        }
    }

    fn drain(&self) {
        while let Some(value) = RETIRED.with(|slot| {
            let mut values = ManuallyDrop::into_inner(slot.take()?);
            let value = values.pop();
            if value.is_some() {
                // Keep the drain active while the destructor can enqueue more work.
                slot.set(Some(ManuallyDrop::new(values)));
            }
            value
        }) {
            drop(value);
        }
    }
}

impl Drop for RetiredDrain {
    fn drop(&mut self) {
        self.drain();
    }
}

/// A detached batch must be processed on its owner's thread, outside heap locks.
#[must_use]
pub struct PendingMerges {
    values: Vec<Wrapper>,
    owner: PhantomData<std::rc::Rc<()>>,
}

impl PendingMerges {
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn merge(self) -> usize {
        let count = self.values.len();
        drop(self);
        count
    }
}

#[derive(Default)]
pub struct QueueHandle {
    map: dashmap::DashMap<ThreadId, Vec<Wrapper>>,
}

/// Like `std::thread::spawn`, with an explicit merge before returning.
/// All threads also retire their owners at TLS teardown, including during unwinding.
pub fn with_explicit_merge<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T,
    F: Send + 'static,
    T: Send + 'static,
{
    std::thread::spawn(|| {
        QueueHandle::register_thread();
        let res = f();
        QueueHandle::finish_thread_merge();
        res
    })
}

pub trait BiasedMerge {
    fn merge(self);
    fn meta_outer(&self) -> &RcWord;
    unsafe fn drop_contents_and_maybe_box_outer(&mut self);
}

impl<T: ?Sized> BiasedMerge for BiasedRc<T> {
    fn merge(self) {
        if self.meta().is_owner() {
            self.meta().merge_counts(false);
        }
        drop(self);
    }

    fn meta_outer(&self) -> &RcWord {
        self.meta()
    }

    unsafe fn drop_contents_and_maybe_box_outer(&mut self) {
        unsafe { self.drop_contents_and_maybe_box() }
    }
}

pub static QUEUE: LazyLock<QueueHandle> = LazyLock::new(QueueHandle::default);

/// Registers this thread. Allocating a biased value also registers it automatically.
pub fn register_thread() {
    QueueHandle::register_thread();
}

impl QueueHandle {
    pub fn register_thread() {
        let _ = ThreadId::current_thread();
    }

    fn enqueue<T: ?Sized + 'static>(value: &BiasedRc<T>) {
        let key =
            ThreadId(NonZeroUsize::new(value.meta().thread_id.load(Ordering::Relaxed)).unwrap());
        let pending = Wrapper(Box::new(ManuallyDrop::new(BiasedRc::from_inner(value.ptr))));
        if let Some(mut queue) = QUEUE.map.get_mut(&key) {
            queue.push(pending);
            return;
        }
        // The registry lock synchronizes with retirement; no owner can update local counts.
        RetiredDrain::enqueue(pending);
    }

    pub fn take_pending() -> PendingMerges {
        let values = ThreadId::current_thread()
            .and_then(|id| {
                QUEUE
                    .map
                    .get_mut(&id)
                    .map(|mut queue| mem::take(&mut *queue))
            })
            .unwrap_or_default();
        PendingMerges {
            values,
            owner: PhantomData,
        }
    }

    pub fn run_explicit_merge() -> usize {
        Self::take_pending().merge()
    }

    /// Drains pending work without retiring a still-running owner.
    pub fn finish_thread_merge() {
        Self::run_explicit_merge();
    }

    pub fn explicit_merge(values: &mut Vec<Wrapper>) -> usize {
        let values = mem::take(values);
        let count = values.len();
        drop(values);
        count
    }
}

impl BiasedRc<dyn Any> {
    #[inline]
    pub fn downcast<T: Any>(self) -> Result<BiasedRc<T>, Self> {
        if (*self).is::<T>() {
            let ptr = self.ptr.cast::<RcBox<T>>();
            mem::forget(self);
            Ok(BiasedRc::from_inner(ptr))
        } else {
            Err(self)
        }
    }
}

impl BiasedRc<dyn Any + Sync + Send> {
    #[inline]
    pub fn downcast<T: Any + Sync + Send>(self) -> Result<BiasedRc<T>, Self> {
        if (*self).is::<T>() {
            let ptr = self.ptr.cast::<RcBox<T>>();
            mem::forget(self);
            Ok(BiasedRc::from_inner(ptr))
        } else {
            Err(self)
        }
    }
}

impl<T: Any + 'static> From<BiasedRc<T>> for BiasedRc<dyn Any + 'static> {
    #[inline]
    fn from(src: BiasedRc<T>) -> Self {
        let ptr = src.ptr.as_ptr() as *mut RcBox<dyn Any>;
        mem::forget(src);
        Self::from_inner(unsafe { NonNull::new_unchecked(ptr) })
    }
}

impl<T: Any + Sync + Send + 'static> From<BiasedRc<T>>
    for BiasedRc<dyn Any + Sync + Send + 'static>
{
    #[inline]
    fn from(src: BiasedRc<T>) -> Self {
        let ptr = src.ptr.as_ptr() as *mut RcBox<dyn Any + Sync + Send>;
        mem::forget(src);
        Self::from_inner(unsafe { NonNull::new_unchecked(ptr) })
    }
}

impl<T: ?Sized> RcBox<T> {
    /// Deallocates an `RcBox`
    ///
    /// `meta` will be dropped, but `data` must have already been dropped in place.
    ///
    /// # Safety
    /// The allocation must have been previously allocated with `RcBox::allocate_*()`.
    #[inline]
    unsafe fn dealloc(ptr: NonNull<RcBox<T>>) {
        unsafe { ptr::addr_of_mut!((*ptr.as_ptr()).rcword).drop_in_place() };
        let layout = Layout::for_value(unsafe { ptr.as_ref() });
        unsafe { alloc::dealloc(ptr.as_ptr().cast(), layout) };
    }

    /// Get the pointer to a `RcBox<T>` from a pointer to the data
    ///
    /// # Safety
    ///
    /// The pointer must point to (and have valid metadata for) the data part of a previously
    /// valid instance of `RcBox<T>` and it must not be dangling.
    #[inline]
    unsafe fn ptr_from_data_ptr(ptr: *const T) -> *const RcBox<T> {
        // Calculate layout of RcBox<T> without `data` tail, but including padding
        let base_layout = Layout::new::<RcBox<()>>();
        // Safety: covered by the safety contract above
        let value_alignment = mem::align_of_val(unsafe { &*ptr });
        let value_offset_layout =
            Layout::from_size_align(0, value_alignment).expect("invalid memory layout");
        let layout = base_layout
            .extend(value_offset_layout)
            .expect("invalid memory layout")
            .0;

        // Move pointer to point to the start of the original RcBox<T>
        // Safety: covered by the safety contract above
        let rcbox = unsafe { ptr.cast::<u8>().offset(-(layout.size() as isize)) };
        set_ptr_value(ptr, rcbox as *mut u8) as *const RcBox<T>
    }
}

impl<T> RcBox<T> {
    /// Tries to allocate an `RcBox`
    ///
    /// Returns a mutable reference with arbitrary lifetime on success and the memory layout that
    /// could not be allocated if the allocation failed.
    #[inline]
    fn try_allocate(meta: RcWord) -> Result<NonNull<RcBox<mem::MaybeUninit<T>>>, Layout> {
        let layout = Layout::new::<RcBox<T>>();

        let ptr = unsafe { alloc::alloc(layout) }.cast::<RcBox<mem::MaybeUninit<T>>>();
        if ptr.is_null() {
            Err(layout)
        } else {
            unsafe { ptr::addr_of_mut!((*ptr).rcword).write(meta) };
            Ok(unsafe { NonNull::new_unchecked(ptr) })
        }
    }

    /// Allocates an `RcBox`
    ///
    /// Returns a mutable reference with arbitrary lifetime on success.
    ///
    /// # Panics
    /// Panics or aborts if the allocation failed.
    #[inline]
    fn allocate(meta: RcWord) -> NonNull<RcBox<mem::MaybeUninit<T>>> {
        match Self::try_allocate(meta) {
            Ok(result) => result,
            Err(layout) => alloc::handle_alloc_error(layout),
        }
    }

    /// Tries to allocate an `RcBox` for a slice.
    ///
    /// Returns a mutable reference with arbitrary lifetime on success and the memory layout that
    /// could not be allocated if the allocation failed or the layout calculation overflowed.
    #[inline]
    fn try_allocate_slice<'a>(
        meta: RcWord,
        len: usize,
        zeroed: bool,
    ) -> Result<&'a mut RcBox<[mem::MaybeUninit<T>]>, Layout> {
        // Calculate memory layout
        let layout = Layout::new::<RcBox<[T; 0]>>();
        let payload_layout = Layout::array::<T>(len).map_err(|_| layout)?;
        let layout = layout
            .extend(payload_layout)
            .map_err(|_| layout)?
            .0
            .pad_to_align();

        // Allocate memory
        let ptr = unsafe {
            if zeroed {
                alloc::alloc_zeroed(layout)
            } else {
                alloc::alloc(layout)
            }
        };

        // Build a fat pointer
        // The immediate slice reference [MaybeUninit<u8>] *should* be sound
        let ptr = ptr::slice_from_raw_parts_mut(ptr.cast::<mem::MaybeUninit<u8>>(), len)
            as *mut RcBox<[mem::MaybeUninit<T>]>;

        if ptr.is_null() {
            // Allocation failed
            Err(layout)
        } else {
            // Initialize metadata field and return result
            unsafe { ptr::addr_of_mut!((*ptr).rcword).write(meta) };
            Ok(unsafe { ptr.as_mut().unwrap() })
        }
    }

    /// Allocates an `RcBox` for a slice
    ///
    /// Returns a mutable reference with arbitrary lifetime on success.
    ///
    /// # Panics
    /// Panics or aborts if the allocation failed or the memory layout calculation overflowed.
    #[inline]
    fn allocate_slice<'a>(
        meta: RcWord,
        len: usize,
        zeroed: bool,
    ) -> &'a mut RcBox<[mem::MaybeUninit<T>]> {
        match Self::try_allocate_slice(meta, len, zeroed) {
            Ok(result) => result,
            Err(layout) => alloc::handle_alloc_error(layout),
        }
    }
}

impl<T> RcBox<mem::MaybeUninit<T>> {
    /// Converts to a mutable reference without the `MaybeUninit` wrapper.
    ///
    /// # Safety
    /// The payload must have been fully initialized or this causes immediate undefined behaviour.
    #[inline]
    unsafe fn assume_init(&mut self) -> &mut RcBox<T> {
        unsafe { (self as *mut Self).cast::<RcBox<T>>().as_mut() }.unwrap()
    }
}

impl<T> RcBox<[mem::MaybeUninit<T>]> {
    /// Converts to a mutable reference without the `MaybeUninit` wrapper.
    ///
    /// # Safety
    /// The payload slice must have been fully initialized or this causes immediate undefined
    /// behaviour.
    #[inline]
    unsafe fn assume_init(&mut self) -> &mut RcBox<[T]> {
        unsafe { (self as *mut _ as *mut RcBox<[T]>).as_mut() }.unwrap()
    }
}

/// Reimplementation of `ptr::set_ptr_value` as long as that one is unstable
///
/// Constructs a new pointer to `addr_ptr` with the metadata and type of `meta_ptr`.
#[inline]
fn set_ptr_value<T: ?Sized, U>(mut meta_ptr: *const T, addr_ptr: *mut U) -> *mut T {
    let thin = (&mut meta_ptr as *mut *const T).cast::<*const u8>();
    // Safety: In case of a thin pointer, this operations is identical
    // to a simple assignment. In case of a fat pointer, with the current
    // fat pointer layout implementation, the first field of such a
    // pointer is always the data pointer, which is likewise assigned.
    unsafe { *thin = addr_ptr.cast() };

    meta_ptr as *mut T
}

pub struct BiasedRc<T: ?Sized + 'static> {
    ptr: NonNull<RcBox<T>>,
    phantom2: PhantomData<T>,
}

impl<T: ?Sized + Clone> BiasedRc<T> {
    #[must_use]
    pub fn make_mut(this: &mut Self) -> &mut T {
        if !this.get_box().has_unique_ref() {
            // Another pointer exists; clone
            *this = Self::new(T::clone(this.data()));
        }

        unsafe {
            // This unsafety is ok because we're guaranteed that the pointer
            // returned is the *only* pointer that will ever be returned to T. Our
            // reference count is guaranteed to be 1 at this point, and we required
            // the Arc itself to be `mut`, so we're returning the only possible
            // reference to the inner data.
            Self::get_mut_unchecked(this)
        }
    }
}

impl<T: ?Sized> BiasedRc<T> {
    #[inline(always)]
    fn from_inner(ptr: NonNull<RcBox<T>>) -> Self {
        Self {
            ptr,
            phantom2: PhantomData,
        }
    }

    #[inline(always)]
    fn get_box(&self) -> &RcBox<T> {
        unsafe { &(*self.ptr.as_ptr()) }
    }

    /// Provides a reference to the inner value.
    #[inline(always)]
    fn data(&self) -> &T {
        unsafe { &(*self.ptr.as_ptr()).data }
    }

    /// Provides a reference to the shared metadata.
    #[inline(always)]
    fn meta(&self) -> &RcWord {
        unsafe { &(*self.ptr.as_ptr()).rcword }
    }

    #[inline(always)]
    unsafe fn pin_get_ref(this: &Pin<Self>) -> &Self {
        // SAFETY: Pin is repr(transparent) and by contract the caller doesn't use the reference
        // to move the value.
        unsafe { &*(this as *const Pin<Self>).cast::<Self>() }
    }

    #[must_use]
    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        unsafe { &mut (*this.ptr.as_ptr()).data }
    }

    #[must_use]
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if this.get_box().has_unique_ref() {
            unsafe { Some(Self::get_mut_unchecked(this)) }
        } else {
            None
        }
    }

    #[must_use]
    #[inline]
    pub fn as_ptr(this: &Self) -> *const T {
        let ptr = this.ptr.as_ptr();

        // Safety: Neccessary for `from_raw()` (when implemented), retains provenance.
        // Besides that, does basically the same thing as `data()` or `get_mut_unchecked()`.
        unsafe { ptr::addr_of_mut!((*ptr).data) }
    }

    #[must_use = "Memory will leak if the result is not used"]
    pub fn into_raw(this: Self) -> *const T {
        let ptr = Self::as_ptr(&this);
        mem::forget(this);
        ptr
    }

    pub unsafe fn from_raw(ptr: *const T) -> Self {
        // Safety: covered by the safety contract for this function
        let box_ptr = unsafe { RcBox::<T>::ptr_from_data_ptr(ptr) };

        Self::from_inner(NonNull::new(box_ptr as *mut _).expect("invalid pointer"))
    }

    #[inline]
    pub fn ptr_eq(this: &Self, other: &BiasedRc<T>) -> bool {
        std::ptr::eq(this.ptr.as_ptr(), other.ptr.as_ptr())
    }

    #[inline]
    pub fn ptr_eq_pin(this: &Pin<Self>, other: &Pin<BiasedRc<T>>) -> bool {
        // SAFETY: we are not moving anything and we don't expose any pointers.
        let this = unsafe { Self::pin_get_ref(this) };
        let other = unsafe { BiasedRc::<T>::pin_get_ref(other) };
        std::ptr::eq(this.ptr.as_ptr(), other.ptr.as_ptr())
    }

    #[inline]
    pub fn strong_count(this: &Self) -> usize {
        let meta = this.meta();
        let word = meta.shared.load(Ordering::Acquire);
        if word.is_merged() {
            word.get_counter() as usize + usize::from(word.is_queued())
        } else if meta.is_owner() {
            (meta.biased_counter.get() as i32 + word.get_counter()) as usize
                + usize::from(word.is_queued())
        } else {
            // A foreign thread cannot read the owner's local counter.
            2
        }
    }

    /// Gets the approximate number of strong pointers to the pinned inner value.
    ///
    #[inline]
    pub fn strong_count_pin(this: &Pin<Self>) -> usize {
        // SAFETY: We are not moving anything and we don't expose any pointers.
        let this = unsafe { Self::pin_get_ref(this) };
        Self::strong_count(this)
    }

    #[inline]
    fn build_new_meta() -> RcWord {
        RcWord::new()
    }

    unsafe fn drop_contents_and_maybe_box(&mut self) {
        // Safety: only called if this was the last strong reference
        unsafe {
            ptr::drop_in_place(Self::get_mut_unchecked(self));
        }

        // Safety: only called if this was the last (weak) reference
        unsafe {
            RcBox::dealloc(self.ptr);
        }
    }
}

impl<T> BiasedRc<T> {
    #[inline]
    pub fn new(data: T) -> Self {
        // register_thread();
        let mut inner = RcBox::allocate(Self::build_new_meta());
        let inner = unsafe { inner.as_mut() };
        inner.data.write(data);
        Self::from_inner(unsafe { inner.assume_init() }.into())
    }

    pub fn new_branded(data: T) -> Self {
        register_thread();
        Self::new(data)
    }

    #[inline]
    pub fn new_uninit() -> BiasedRc<mem::MaybeUninit<T>> {
        let inner = RcBox::allocate(Self::build_new_meta());
        BiasedRc::from_inner(inner)
    }

    #[inline]
    pub fn new_zeroed() -> BiasedRc<mem::MaybeUninit<T>> {
        let mut inner = RcBox::allocate(Self::build_new_meta());
        unsafe { inner.as_mut() }.data = mem::MaybeUninit::zeroed();
        BiasedRc::from_inner(inner)
    }

    #[inline]
    pub fn pin(data: T) -> Pin<Self> {
        unsafe { Pin::new_unchecked(Self::new(data)) }
    }

    pub fn try_new(data: T) -> Result<Self, AllocError> {
        let mut inner = RcBox::try_allocate(Self::build_new_meta()).map_err(|_| AllocError)?;
        let inner = unsafe { inner.as_mut() };
        inner.data.write(data);
        Ok(Self::from_inner(unsafe { inner.assume_init() }.into()))
    }

    pub fn try_new_uninit() -> Result<BiasedRc<mem::MaybeUninit<T>>, AllocError> {
        let inner = RcBox::try_allocate(Self::build_new_meta()).map_err(|_| AllocError)?;
        Ok(BiasedRc::from_inner(inner.into()))
    }

    pub fn try_new_zeroed() -> Result<BiasedRc<mem::MaybeUninit<T>>, AllocError> {
        let mut inner = RcBox::try_allocate(Self::build_new_meta()).map_err(|_| AllocError)?;
        unsafe { inner.as_mut() }.data = mem::MaybeUninit::zeroed();
        Ok(BiasedRc::from_inner(inner))
    }

    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        if !this.get_box().has_unique_ref() {
            return Err(this);
        }
        let copy = unsafe { ptr::read(Self::as_ptr(&this)) };
        unsafe { RcBox::dealloc(this.ptr) };
        mem::forget(this);
        Ok(copy)
    }
}

/// The `AllocError` error indicates an allocation failure when using `try_new()` etc.
///
/// Will become a type alias for [`std::alloc::AllocError`] once that is stabilized.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct AllocError;

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

impl std::error::Error for AllocError {}

impl From<Infallible> for AllocError {
    fn from(_: Infallible) -> AllocError {
        unreachable!();
    }
}

impl<T: ?Sized> Deref for BiasedRc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.data()
    }
}

impl<T: ?Sized> Borrow<T> for BiasedRc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for BiasedRc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> Clone for BiasedRc<T> {
    #[inline]
    fn clone(&self) -> Self {
        self.get_box().increment();
        Self::from_inner(self.ptr)
    }
}

impl<T: ?Sized + 'static> Drop for BiasedRc<T> {
    #[inline]
    fn drop(&mut self) {
        match self.get_box().decrement() {
            DecrementAction::DoNothing => {}
            DecrementAction::Queue => {
                // Enqueue the value
                QueueHandle::enqueue(self);
            }
            DecrementAction::Deallocate => {
                unsafe { self.drop_contents_and_maybe_box() };
            }
        }
    }
}

// Propagate some useful traits implemented by the inner type

impl<T: Default> Default for BiasedRc<T> {
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq> PartialEq<BiasedRc<T>> for BiasedRc<T> {
    #[inline]
    fn eq(&self, other: &BiasedRc<T>) -> bool {
        **self == **other
    }
}

impl<T: ?Sized + Eq> Eq for BiasedRc<T> {}

impl<T: ?Sized + Hash> Hash for BiasedRc<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Self::data(self).hash(state);
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd<BiasedRc<T>> for BiasedRc<T> {
    #[inline]
    fn partial_cmp(&self, other: &BiasedRc<T>) -> Option<cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + Ord> Ord for BiasedRc<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for BiasedRc<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&Self::data(self), f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for BiasedRc<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&Self::data(self), f)
    }
}

impl<T: ?Sized> fmt::Pointer for BiasedRc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&Self::as_ptr(self), f)
    }
}

impl<T: ?Sized> Unpin for BiasedRc<T> {}

unsafe impl<T: ?Sized + Sync + Send> Send for BiasedRc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for BiasedRc<T> {}

impl<T> iter::FromIterator<T> for BiasedRc<[T]> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        let vec: Vec<T> = iter.into_iter().collect();
        vec.into()
    }
}

impl<T> BiasedRc<[T]> {
    /// Creates a new reference-counted slice with uninitialized contents.
    #[inline]
    pub fn new_uninit_slice(len: usize) -> BiasedRc<[mem::MaybeUninit<T>]> {
        let inner = RcBox::allocate_slice(Self::build_new_meta(), len, false);
        BiasedRc::from_inner(inner.into())
    }

    /// Creates a new reference-counted slice with uninitialized contents, with the memory being
    /// filled with 0 bytes.
    #[inline]
    pub fn new_zeroed_slice(len: usize) -> BiasedRc<[mem::MaybeUninit<T>]> {
        let inner = RcBox::allocate_slice(Self::build_new_meta(), len, true);
        BiasedRc::from_inner(inner.into())
    }

    #[inline]
    unsafe fn copy_from_slice_unchecked(src: &[T]) -> Self {
        let len = src.len();
        let inner = RcBox::allocate_slice(Self::build_new_meta(), len, false);
        let dest = ptr::addr_of_mut!((*inner).data).cast();

        // Safety: The freshly allocated `RcBox` can't alias `src` and the payload can be fully
        // initialized by copying the slice memory. The copying is also safe as long as the safety
        // requirements for calling this are fulfilled.
        unsafe {
            src.as_ptr().copy_to_nonoverlapping(dest, src.len());
            BiasedRc::from_inner(inner.assume_init().into())
        }
    }
}

impl<T: Copy> BiasedRc<[T]> {
    #[inline]
    pub fn copy_from_slice(src: &[T]) -> Self {
        // Safety: `T` is `Copy`.
        unsafe { Self::copy_from_slice_unchecked(src) }
    }
}

#[must_use]
pub(crate) struct SliceBuilder<'a, T> {
    rcbox: &'a mut RcBox<[MaybeUninit<T>]>,
    n_elems: usize,
}

impl<'a, T> SliceBuilder<'a, T> {
    /// Constructs a new builder for a `RcBox<[T]>` with a slice length of `length`
    #[inline]
    pub fn new(meta: RcWord, length: usize) -> Self {
        let rcbox = RcBox::<T>::allocate_slice(meta, length, false);
        Self { rcbox, n_elems: 0 }
    }

    /// Fills the next free slot in the slice with `item`
    #[inline]
    pub fn append(&mut self, item: T) {
        self.rcbox.data[self.n_elems].write(item);
        self.n_elems += 1;
    }

    /// Consumes the builder and returns the initialized `RcBox<T>`
    ///
    /// The result is a mutable reference with arbitrary lifetime.
    ///
    /// # Panics
    /// Panics if the number of appended elements doesn't match the promised length.
    #[inline]
    pub fn finish(self) -> &'a mut RcBox<[T]> {
        assert_eq!(self.n_elems, self.rcbox.data.len());
        let rcbox: *mut _ = self.rcbox;
        std::mem::forget(self);
        unsafe { (*rcbox).assume_init() }
    }
}

impl<T> Drop for SliceBuilder<'_, T> {
    /// Drops the already cloned elements and deallocates the temporary `RcBox`
    ///
    /// Only reached if the builder wasn't consumed by `finish`, which should only happen in
    /// a panic unwind.
    #[cold]
    fn drop(&'_ mut self) {
        let slice = &mut self.rcbox.data[..self.n_elems];
        unsafe {
            let slice: &mut [T] = &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]);
            drop_in_place(slice);
        }
        unsafe {
            RcBox::dealloc(self.rcbox.into());
        }
    }
}

impl<T> From<T> for BiasedRc<T> {
    #[inline]
    fn from(src: T) -> Self {
        Self::new(src)
    }
}

impl<T: Clone> From<&[T]> for BiasedRc<[T]> {
    #[inline]
    fn from(src: &[T]) -> Self {
        let mut builder = SliceBuilder::new(Self::build_new_meta(), src.len());
        for item in src {
            builder.append(Clone::clone(item));
        }
        Self::from_inner(builder.finish().into())
    }
}

impl<T> From<Vec<T>> for BiasedRc<[T]> {
    #[inline]
    fn from(mut src: Vec<T>) -> Self {
        unsafe {
            let result = BiasedRc::<_>::copy_from_slice_unchecked(&src[..]);

            // Set the length of `src`, so that the moved items are not dropped.
            src.set_len(0);

            result
        }
    }
}

impl From<&str> for BiasedRc<str> {
    #[inline]
    fn from(src: &str) -> Self {
        let bytes = BiasedRc::<_>::copy_from_slice(src.as_bytes());
        let inner = unsafe { (bytes.ptr.as_ptr() as *mut _ as *mut RcBox<str>).as_mut() }.unwrap();
        mem::forget(bytes);
        Self::from_inner(inner.into())
    }
}

impl From<String> for BiasedRc<str> {
    #[inline]
    fn from(src: String) -> Self {
        Self::from(&src[..])
    }
}

#[test]
fn does_this_work() {
    register_thread();
    let value = BiasedRc::new(10);
    println!("{}", value);
}

#[test]
fn test_drop_impl() {
    struct Foo {
        foo: usize,
    }
    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Calling drop: {}", self.foo);
        }
    }
    let value = BiasedRc::new(Foo { foo: 10 });

    drop(value);
}

#[test]
fn test_clone_impl() {
    register_thread();
    struct Foo {
        foo: usize,
    }
    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Calling drop: {}", self.foo);
        }
    }
    let value = BiasedRc::new(Foo { foo: 10 });
    let cloned = BiasedRc::clone(&value);

    drop(value);

    println!("Now we're done");

    drop(cloned);
}

#[test]
fn test_queue_impl() {
    register_thread();
    struct Foo {
        foo: String,
    }
    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Calling drop: {}", self.foo);
        }
    }
    let value = BiasedRc::new(Foo {
        foo: "hello world".to_string(),
    });
    let cloned = BiasedRc::clone(&value);

    let thread = std::thread::spawn(move || {
        drop(cloned);

        // Run explicit merge:
        QueueHandle::run_explicit_merge();
    });

    thread.join().unwrap();

    QueueHandle::run_explicit_merge();
}

#[test]
fn test_try_unwrap_impl_same_thread() {
    #[derive(Debug)]
    struct Foo {
        foo: String,
    }
    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Calling drop: {}", self.foo);
        }
    }
    let value = BiasedRc::new(Foo {
        foo: "hello world".to_string(),
    });
    let cloned = BiasedRc::clone(&value);

    let failed_unwrap = BiasedRc::try_unwrap(value).unwrap_err();

    drop(failed_unwrap);

    assert!(BiasedRc::try_unwrap(cloned).is_ok());

    // let thread = std::thread::spawn(move || {
    //     drop(cloned);

    //     // Run explicit merge:
    //     QueueHandle::run_explicit_merge();
    // });

    // thread.join().unwrap();

    // QueueHandle::run_explicit_merge();
}

#[test]
fn test_try_unwrap_impl_moved_thread() {
    #[derive(Debug)]
    struct Foo {
        foo: String,
    }
    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Calling drop: {}", self.foo);
        }
    }
    let value = BiasedRc::new(Foo {
        foo: "hello world".to_string(),
    });
    let cloned = BiasedRc::clone(&value);

    let failed_unwrap = BiasedRc::try_unwrap(value).unwrap_err();

    drop(failed_unwrap);

    assert!(BiasedRc::try_unwrap(cloned).is_ok());

    // let thread = std::thread::spawn(move || {
    //     drop(cloned);

    //     // Run explicit merge:
    //     QueueHandle::run_explicit_merge();
    // });

    // thread.join().unwrap();

    // QueueHandle::run_explicit_merge();
}

#[test]
fn try_unwrap_data_race() {
    let a = BiasedRc::new(0);
    let b = a.clone();

    std::thread::spawn(move || {
        let _value = b;
    });

    std::thread::spawn(move || {
        BiasedRc::try_unwrap(a).unwrap();
    });
}

#[test]
fn try_unwrap_data_race_sleep() {
    // Exists to be exercised by Miri to check for data races.
    let a = BiasedRc::new(0);
    let b = a.clone();
    let t1 = std::thread::spawn(move || {
        let _value = *b;
    });
    let t2 = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(100));
        if let Ok(_) = BiasedRc::try_unwrap(a) {
            // u += 1;
        }
    });
    t1.join().unwrap();
    t2.join().unwrap();
}

#[test]
fn get_mut_data_race_sleep() {
    // Exists to be exercised by Miri to check for data races.
    let mut a = BiasedRc::new(0);
    let b = a.clone();
    let t1 = std::thread::spawn(move || {
        let _value = *b;
    });
    let t2 = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(100));
        if let Some(u) = BiasedRc::get_mut(&mut a) {
            *u += 1;
        }
    });
    t1.join().unwrap();
    t2.join().unwrap();
}

thread_local! {
    static DROP_COUNTER: Cell<usize> = Cell::new(0);
}

#[cfg(test)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Test(u8);

#[cfg(test)]
impl Drop for Test {
    fn drop(&mut self) {
        DROP_COUNTER.with(|x| x.set(x.get() + 1));
    }
}
#[cfg(test)]
impl Default for Test {
    fn default() -> Self {
        Test(1)
    }
}

#[cfg(test)]
// Panicing clone to test cloning from slice error cases
impl Clone for Test {
    fn clone(&self) -> Self {
        if self.0 == 0 {
            panic!();
        }
        Self(self.0)
    }
}

#[test]
fn test_any() {
    let a = BiasedRc::<Test>::new(Test(42));
    let b: BiasedRc<dyn Any> = From::from(a.clone());
    let c: BiasedRc<dyn Any + Send + Sync> = From::from(a);

    assert!(b.clone().downcast::<usize>().is_err());
    assert!(c.clone().downcast::<usize>().is_err());
    let a = c.downcast::<Test>().unwrap();
    assert_eq!(a.0, 42);
    let b = b.downcast::<Test>().unwrap();
    assert_eq!(b.0, 42);
}

/*
From the paper:

Lastly, when a thread terminates, it processes the objects re-
maining in its QueuedObjects list, and de-registers itself from
the QueuedObjects structure. Theoretically, an object can out-
live its owner thread if its biased counter is positive, and has not
been queued in the QueuedObjects list when the owner thread
terminates. We handle this case as follows. When a non-owner
thread makes the shared counter of an object negative, it first
checks whether the object’s owner thread is alive by looking-up
the QueuedObjects structure — which implicitly records the live
threads. If the owner thread is not alive, the non-owner thread
merges the counters instead of queuing the object, and either deal-
locates the object or unbiases it
*/
#[test]
fn test_moving_across_threads() {
    let (sender, receiver) = std::sync::mpsc::channel::<BiasedRc<usize>>();

    let (send_finish, receive_finish) = std::sync::mpsc::channel::<()>();

    let start = std::thread::spawn(move || {
        // register_thread();
        let value = BiasedRc::new(0);
        sender.send(value.clone()).unwrap();
        receive_finish.recv().unwrap();

        let _ = value.clone();
        let _ = value.clone();

        drop(value);
    });

    let value = receiver.recv().unwrap();
    dbg!(value.get_box().rcword.biased_counter.get());
    let meta = value.get_box().rcword.shared.load(Ordering::Relaxed);
    dbg!(meta.get_merged());
    dbg!(meta.get_queued());
    dbg!(meta.get_counter());

    // Okay, so now we're in the realm of a value which has escaped its
    // owner thread, but the value has not been enqueued. At this point
    // now it should be clear that the thread is dead, because we've marked it
    // as such?
    dbg!(value.get_box().rcword.is_owner());

    drop(value);

    send_finish.send(()).unwrap();

    // Value should be on the thread:
    let merged = QueueHandle::run_explicit_merge();
    start.join().unwrap();

    dbg!(merged);
}

#[test]
fn test_dropping_across_multiple_threads() {
    register_thread();
    let original_value = BiasedRc::new("value".to_string());

    let value_one = original_value.clone();
    let other_thread_1 = std::thread::spawn(move || {
        register_thread();
        let value = value_one;

        for _ in 0..1000 {
            let _ = value.clone();
        }

        drop(value);
    });

    let value_one = original_value.clone();
    let other_thread_2 = std::thread::spawn(move || {
        let value = value_one;

        for _ in 0..1000 {
            let _ = value.clone();
        }

        drop(value);
    });

    other_thread_1.join().unwrap();
    other_thread_2.join().unwrap();

    let mut values = Vec::new();

    for _ in 0..100 {
        values.push(original_value.clone());
    }

    drop(original_value);

    values.clear();

    QueueHandle::run_explicit_merge();
}

#[test]
fn static_values() {
    static ROOT: LazyLock<BiasedRc<String>> = LazyLock::new(|| BiasedRc::new("Hello".to_string()));
    register_thread();

    with_explicit_merge(|| {
        let mut foo = ROOT.clone();

        let new = BiasedRc::make_mut(&mut foo);
        *new = "foo".to_string();

        assert_eq!(foo.data(), "foo");
        assert_eq!(ROOT.data(), "Hello");

        drop(foo);
    });

    with_explicit_merge(|| {
        let mut foo = ROOT.clone();

        let new = BiasedRc::make_mut(&mut foo);
        *new = "foo".to_string();

        drop(foo);
    });

    with_explicit_merge(|| {
        register_thread();
        let mut foo = ROOT.clone();

        let new = BiasedRc::make_mut(&mut foo);
        *new = "foo".to_string();

        drop(foo);
    })
    .join()
    .unwrap();

    with_explicit_merge(|| {
        register_thread();
        let foo = ROOT.clone();
        drop(foo);
    })
    .join()
    .unwrap();

    let foo = ROOT.clone();
    drop(foo);

    // dbg!(ROOT.get_box().rcword.biased_counter.get());
    let meta = ROOT.get_box().rcword.shared.load(Ordering::Relaxed);
    dbg!(meta.get_merged());
    dbg!(meta.get_queued());
    dbg!(meta.get_counter());
}

#[test]
fn make_mut_test() {
    let foo = BiasedRc::new("foo".to_string());
    let mut copy = foo.clone();
    let new_thing = BiasedRc::make_mut(&mut copy);

    *new_thing = "hello".to_string();
}

// #[test]
// fn test_merging() {
//     let word = BiasedRc::new(10);
//     drop(word);
// }

#[cfg(test)]
mod lifecycle_tests;
