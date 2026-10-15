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
