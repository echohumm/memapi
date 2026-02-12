#[cfg(feature = "c_alloc")]
/// An allocator which uses C's [`aligned_alloc`](c_alloc::ffi::c_alloc) set of allocation
/// functions.
pub mod c_alloc;
#[cfg(feature = "stack_alloc")]
/// An allocator which uses C's `alloca`/`_alloca` allocation function.
pub mod stack_alloc;

// TODO: basic ptr-inc alloc with a backer + arrayalloc, rename stackalloc for clarity
