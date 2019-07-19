## v0.0.3

- Added `Slab::leak`, a new interface to directly allocate values. Avoid
  requiring `Box` and `Box::leak` from `alloc` and allows usage a `Slab` with
  limited lifetime such as on the stack.

## v0.0.2

- `Slab::take` has been renamed to `Slab::alloc`.
- Added `uninit` and `zeroed` constructors as available for `MaybeUninit`
- Made the `new` constructor safe as no uninitialized bytes are read
- The nightly `try_reserve` feature is now called `nightly_try_reserve`
  Note: It is only used in a test and has no influence on the api
