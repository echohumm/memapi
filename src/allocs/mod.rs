#[cfg(feature = "c_alloc")]
/// An allocator which uses C's [`posix_memalign`](c_alloc::ffi::c_alloc) set of allocation
/// functions.
pub mod c_alloc;
#[cfg(feature = "stack_alloc")]
/// An allocator which uses C's `alloca`/`_alloca` allocation function.
pub mod stack_alloc;

// TODO: Checked<A> which just wraps an allocator and stores allocations to validate deallocations
//  for checked_dealloc?
