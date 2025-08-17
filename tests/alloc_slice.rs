// miri is incompatible with malloc_defaultalloc
#![cfg_attr(feature = "malloc_defaultalloc", cfg(not(miri)))]
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]

// TODO
