Safely pinning a statically allocated task.

# Usage — Pinned tasks

Another use case similar to a pool is the ability to _pin_ objects that have
been allocated without the need for macros or `unsafe`. This is sound because
the memory within a static bump allocator is _never_ reused for any other
purpose.

Let's set the scene by defining a long running task that requires pinning.

```
use static_alloc::Bump;
```
