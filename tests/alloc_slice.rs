// miri is incompatible with malloc_defaultalloc
#![cfg_attr(feature = "malloc_defaultalloc", cfg(not(miri)))]
#![cfg(any(not(feature = "no_alloc"), feature = "malloc_defaultalloc"))]
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]

// TODO
