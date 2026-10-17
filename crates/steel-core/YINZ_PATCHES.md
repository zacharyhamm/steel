# Yinz Steel patches

Source: `steel-core` 0.8.3 from crates.io, upstream `mattwparas/steel` commit
`11a57adcf42c22733463c59b1f44ec49eb7043bc`, directory `crates/steel-core`.
The original package SHA-256 is `1341b81ac9c27acc592a7f76eebeb4a4420d1099d7419f1b1ee9eb7fcca13a15`.
These patches are maintained on the `yinz-0.8.3` branch of `zacharyhamm/steel`.

Compiler and runtime fixes are applied:

- `src/compiler/compiler.rs` and `src/steel_vm/engine.rs`: expose a diagnostic-only
  source name for in-memory programs. Entry-point closures retain their filename
  and line after deferred execution, without canonicalizing a real path or
  granting the compiler a filesystem module origin. Existing path APIs retain
  their original behavior.

- `src/compiler/code_gen.rs`: specialize an integer immediate only when it fits
  the 24-bit instruction payload. Larger positive constants previously panicked
  in debug builds and were silently truncated in release builds.
- `src/steel_vm/const_evaluation.rs`: keep top-level definitions out of constant
  propagation. A later REPL `set!` must be visible to previously defined closures.
  Local lexical constant propagation remains enabled.

- `src/compiler/passes/begin.rs`: delay nonconstant internal definition initializers
  until their position in the body. When a body also defined a local function,
  these initializers previously ran before preceding effects such as `set!`.
  The existing delayed-initializer path preserves mutually recursive functions.

Two deprecated `std::usize::MAX` references in `src/compiler/passes/analysis.rs`
use the equivalent `usize::MAX` spelling to keep the current toolchain warning-free.
The unused `AsRefSteelVal` import in `src/steel_vm/vm/threads.rs` is removed.

GC and persistent-list regressions are in `src/steel_vm/tests.rs`. The full
embedding and confined-worker regressions remain in the Yinz repository under
`yinz-steel/src/unit/`. Remove each patch when an upstream release passes those
regressions.

- `src/values/closed.rs`: release payloads in dead heap slots during collection,
  including after marking. Waiting until a slot is reused retains old snapshots
  and parsed history bodies long after their owners are gone. Grow geometrically
  only when collection leaves the heap full; the former 25,600-slot minimum
  delayed collection of recursive captures beyond the worker's memory budget.

- `src/rvals.rs` and `src/rvals/cycles.rs`: compare complete persistent list nodes,
  including their tails. Appending to a list can share its first storage chunk
  without preserving equality. Equality traversal also uses the whole node identity.

- `primitives/control.rs`: preserve the contents of string arguments to `error`
  and `to-string`. Formatting a string through its Scheme representation escaped
  quotes, newlines, and backslashes again on every caught/rethrown error. Other
  values keep their existing printed representation and leading separators.

- `src/compiler/passes/analysis.rs`: include enclosing lambda arguments when
  propagating capture mutability. A closure created before a later `set!` otherwise
  received an internal box instead of the captured value.
- `src/values/closed.rs`: run the existing synchronous pointer-marking traversal on
  the interpreter thread. The upstream collector lazily spawned one marker thread
  per available CPU in every plugin process; ordinary larger inventories exhausted
  confined workers' address-space budget while starting that pool. Marking retains
  the same root and pointer traversal, then releases the temporary root queue.
  The confined-worker regression keeps a large mutable graph alive across repeated
  collections and verifies its values afterward.

- `src/rvals.rs`: expose a read-only `SteelByteVector::with_bytes` borrowing method.
  The host bridge can decode and transmit binary values without expanding each byte into
  a Scheme integer or JSON number. The callback cannot retain the borrowed slice.

- `src/steel_vm/engine.rs`, `src/steel_vm/vm.rs`, and `src/values/closed.rs`: give
  `Engine::deep_clone` an isolated heap. The copied cells were unreferenced while the
  clone's globals kept pointing into the template heap, so every kernel clone shared
  template boxes and lost them when the template's heap was torn down. The copy now
  rewrites references reachable from the clone's globals, cells, closures, boxes,
  streams, transducers, and reducers into its own cells. Continuations and iterators over
  collections are copied like boxes; an iterator's remaining items are taken once, and the
  template's iterator yields the same items afterward. Custom values and opaque iterators
  stay shared, so `#%global-will-executor` is shared while `#%will-executor-running` is per
  clone. The copy roots each shared value that still reaches a template cell and keeps
  the template's heap, so those values stay valid after the template drops and keep
  sharing its state. Lists are matched by their whole node,
  including the tail, because appending shares the prefix's storage and offset. A list's
  suffixes become views of the rebuilt longest list that contains them, in whichever
  order they are reached, so a retained `cdr` stays `eq?` to the copy's `cdr`. Two lists
  that share a tail only through a linked node are rebuilt separately, because im-lists
  cannot link a new node to an existing view. A closure's contract can refer back to the
  closure, so it is remapped after the rest of the graph and attached to the closure's
  copy. A tail that one of its own list's elements refers to, such as a closure over the
  list it was consed onto, is rebuilt on its own, since the copy it would be a view of
  does not exist yet; that element's tail is then not `eq?` to the copy's `cdr`. Struct
  property maps stay in the shared vtable and other heaps' cells stay shared, so the copy
  retains those that reach template cells, like other shared values.

- `src/values/structs.rs`, `src/values/closed.rs`, and `src/steel_vm/builtin.rs`: trace
  a struct type's properties only when a collection reaches one of its instances, its
  descriptor, its constructor, predicate, or accessors, or a `serialize-value` result
  that refers to it. A registered builtin module traces its values, so a struct function
  exported before it is imported keeps its type's properties. Registering a module
  generates its context-function wrappers without holding the module's lock, which a
  collection on another thread can need meanwhile. Rooting every vtable entry
  pinned the properties of each evaluated local `struct`
  form forever and grew every collection's root set. Same-named types sent to another
  thread resolve to their own descriptor, then to the newest match. Deserialization
  reuses the matched type's current properties, so bytes from `serialized->bytes` alone
  do not keep them; Yinz does not use these functions.

- `src/rvals.rs`: `eq?` and `eqv?` compare boxes, structs, syntax objects, iterators,
  references, big rationals, and complex numbers by identity, and small rationals by
  value, which constant interning also relies on. They previously returned `#f` even
  for the same object.

- `src/rvals.rs` and `src/steel_vm/primitives.rs`: `eqv?` compares big integers, big
  rationals, and complex numbers by value and exactness, as R7RS requires. Comparing them
  by identity missed equal numbers, so `memv` and `assv` did not find matching keys. `eq?`
  and constant interning still compare them by identity, and whatever is `eq?` is also
  `eqv?`, even a complex number with a NaN part.

- `src/values/lists.rs`, `src/rvals/cycles.rs`, and `src/values/closed.rs`: drop lists
  without im-lists' thread-local empty list once that storage is destroyed. Rust does not
  specify thread-local destructor order, so a thread-local that still owns lists, such as
  the vtable, the root table, or an engine stored by the host, can be destroyed after it;
  draining then aborted the thread. A probe list kept in that storage records when it is
  destroyed. From then on, each list's elements are cloned out before its nodes are
  released, so nested lists are still released iteratively. Other drops keep draining,
  which stops at shared nodes. A root released after the root table is ignored.
  Collections and teardown traces borrow a list's elements, since consuming a list also
  builds an empty one in that storage.

- `src/steel_vm/vm/threads.rs` and `src/values/closed.rs`: `thread-join!` copies a result
  from another heap into the joining thread's heap. A pending result's heap is freed once
  its handle is released, so the joined value pointed into a freed heap. Shared values that
  still reach the result's heap keep it, as in deep clones. Boxes, continuations, and
  iterators in the result stay shared too, since the joining engine can hold them as
  well. A join on the same heap is unchanged. A closure keeps its engine's global slots,
  so calling one in an unrelated engine is still unsupported. The copy traces each value
  once, as teardown does.

- `src/steel_vm/vm.rs` and `src/values/closed.rs`: a closed heap keeps what the registered
  roots reach, the same values a live collection keeps for holders outside the heap. A
  value held by another engine or the host stays valid only while its heap is alive and a
  root reaches it; values meant to outlive their engine are rooted, joined, or deep cloned.
  Teardown traces each value once, and a list by its whole node, since two slices can
  share an address; walking each path through lists that share sublists took time
  exponential in their depth. Live collection and global-slot recycling still walk a list
  once per path.

- `src/compiler/compiler.rs`, `src/values/closed.rs`, and `src/steel_vm/engine.rs`: a
  closure reached only through a registered root keeps its global slots from recycling
  only if its compiler generated it. The compiler records the ids of the functions it
  generates, and of deserialized ones and the capture-free lambdas nested in them.
  Recycling also traces the value of each shadowed slot that a traced closure keeps, so
  the slots that value refers to are kept too. Roots are process-wide in sync builds and
  per-thread otherwise, so other engines' rooted closures kept this engine's shadowed slots
  with the same numbers. Engines deep cloned from one template still share the ids
  generated before the clone. Closures reached from the globals keep their slots as before.

- `src/values/closed.rs` and `src/steel_vm/vm.rs`: a collection releases the copies it
  makes of values it does not own once the heap is unlocked, and global-slot recycling once
  the heap and environment are unlocked. Another engine or thread can replace the original
  while the copy is held, so dropping the copy can run that value's destructor, which
  could deadlock if it reentered this heap. That includes native functions and futures,
  which a collection does not otherwise queue. The interner drops lifted pure functions
  only after recycling releases its copies, since a freed slot can hold their last other
  reference. Collections in sync builds still trace every registered root, so they
  briefly hold copies of other engines' values. A collection reads the registered roots
  only after the heap's other threads have stopped, since a thread can root a value right
  up to its safepoint, when its stack no longer holds the value.

- `src/rvals/cycles.rs`: a pair whose fields cannot recurse skips the drop buffer. Car
  is released before cdr is classified, so a child held by both fields still drains
  iteratively when its last reference goes.

- `src/values/closed.rs`, `src/steel_vm/vm.rs`, and `src/steel_vm/vm/threads.rs`: a heap
  that retains another heap's shared values for a deep clone or a joined result releases
  each one once its own collection no longer reaches it, and the other heap's storage once
  it reaches none of that heap's cells. Retaining them for the heap's whole life kept
  every discarded payload. A cell of the other heap that the collection still reaches
  directly is rooted instead, until it is no longer ordinarily reachable, so will keys
  stay weak. Only the other heap traces these roots: a heap that traced its own, or a
  sibling clone's, would keep them reachable forever. A clone and a joined result also
  retain what their source heap retains, since their copied cells can reach it. Releasing
  them runs destructors after the heap is unlocked.

- `src/values/closed.rs`: `will-register` records the heap it was called from, which it
  reads without the heap lock: waiting for that lock is a safepoint, and the arguments have
  already left the VM stack, so another thread's collection would not see them. A
  collection decides a key's readiness from its own reachability only for keys it owns,
  and otherwise from the key's reference count, since another heap's collection does not
  trace the owner's roots and marked live keys ready. Keys registered from Rust with
  `WillExecutor::register` have no owner and use the reference count.
