# AGENTS.md

> [!IMPORTANT]
> **This branch only supports Yinz, and Yinz only runs Steel in no-kernel mode.**
>
> Every engine Yinz creates comes from `Engine::new_raw_no_kernel()`
> (see `yinz-steel/src/sandbox.rs` in the Yinz repo), so the compiler's
> `kernel` is always `None`. Kernel mode (`Engine::new()`, `new_sandboxed()`,
> `new_base()`, `new_raw()`) is out of scope here:
>
> - Judge correctness by no-kernel behavior. Reproduce and test with
>   `Engine::new_raw_no_kernel()`.
> - Don't spend effort fixing, reviewing, or reporting bugs that only happen
>   with a kernel.
> - Don't hold back a no-kernel fix just because the matching kernel-mode
>   behavior differs or stays broken.
> - Kernel-only features such as `defmacro` and `begin-for-syntax` don't exist
>   for Yinz. `struct` and `define-values` come from the native Rust lowering
>   in `crates/steel-core/src/parser/expand_visitor.rs`, not from
>   `scheme/kernel.scm`.
