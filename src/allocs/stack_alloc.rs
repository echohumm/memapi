use {
    crate::{Layout, error::Error, ffi::stack_alloc::with_alloca},
    core::ptr::NonNull
};

// TODO: make this faster, make sure it works in all situations

/// An allocator which uses C's `alloca` allocation method.
///
/// # WARNING
///
/// This is experimental. The C code and ffi backing this are custom, and I don't know C, so this
/// may or may not work. As far as I can tell, it works, but use at your own risk until I have
/// properly validated this is fine.
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
/// - if compiling with a Rust version below `1.71` and the `catch_unwind` feature is disabled, the
///   `with_mem` function passed to allocation methods must never unwind.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackAlloc;

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
