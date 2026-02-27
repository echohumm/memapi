#[cfg(feature = "c_alloc")]
/// An allocator which uses C's `posix_memalign`] on Unix, and `_aligned_malloc` on windows.
pub mod c_alloc;
#[cfg(feature = "stack_alloc")]
/// An allocator which uses C's `alloca`/`_alloca` allocation function.
pub mod stack_alloc;

// TODO: Checked<A> which just wraps an allocator and stores allocations to validate ops for
//  Checked... traits? note specialization over whether A: Checked... would be nice
