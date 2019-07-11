## v0.0.2

- `Slab::take` has been renamed to `Slab::alloc`.
- Added `uninit` and `zeroed` constructors as available for `MaybeUninit`
- Made the `new` constructor safe as no uninitialized bytes are read
- The nightly `try_reserve` feature is now called `nightly_try_reserve`
  Note: It is only used in a test and has no influence on the api
