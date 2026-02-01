use {
    crate::{Layout, error::Error, ffi::stack_alloc::with_alloca},
    core::ptr::NonNull
};

/// An allocator which uses C's `alloca` allocation method.
///
/// # WARNING
///
/// This is experimental. The C code and ffi backing this is custom, and I don't know C so this may
/// or may not work. As far as I can tell, it works, but use at your own risk until I have properly
/// validated this is fine.
///
/// # Note
///
/// Allocations made by this allocator are aligned by allocating extra space and manually aligning
/// within that space.
///
/// If `size + (align - 1)` exceeds the stack allocation limit, a stack overflow will occur.
///
/// # Safety
///
/// The caller must ensure:
/// - attempting to allocate <code>[layout.size()](Layout::size) + ([layout.align()](Layout::align)
///   \- 1)</code> bytes on the stack will not cause a stack overflow.
/// - the `with_mem` parameter passed to implemented methods will _never_ unwind, only abort or
///   return.
pub struct StackAlloc;

// TODO: clean up the whole alloca implementation

impl crate::AllocTemp for StackAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        // TODO: remove function arg
        with_alloca(layout, false, |ptr, uninit: *mut R| {
            uninit.write(with_mem(ptr));
        })
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        with_alloca(layout, true, |ptr, uninit: *mut R| {
            uninit.write(with_mem(ptr));
        })
    }
}

pub use crate::ffi::stack_alloc as ffi;
