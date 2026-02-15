use {
    crate::{
        error::Error,
        ffi::stack_alloc::with_alloca,
        layout::Layout,
        traits::alloc_temp::AllocTemp
    },
    ::core::{
        ops::FnOnce,
        ptr::{self, NonNull},
        result::Result
    }
};

/// An allocator that uses C's `alloca` for stack allocation.
///
/// This satisfies the requested alignment by allocating extra space and aligning within it. Ensure
/// <code>[layout.size()](Layout::size) + ([layout.align()](Layout::align) - 1)</code> does not
/// exceed the stack limit to avoid overflow.
///
/// # Safety
///
/// The caller must ensure:
/// - attempting to allocate <code>[layout.size()](Layout::size) + ([layout.align()](Layout::align)
///   \- 1)</code> bytes on the stack will not cause a stack overflow.
/// - if compiling with a Rust version below `1.71` and the `catch_unwind` feature is disabled, the
///   `with_mem` function passed to allocation methods will never unwind.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackAlloc;

impl AllocTemp for StackAlloc {
    type Error = Error;

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        with_alloca(layout, |ptr, uninit: *mut R| {
            ptr::write(uninit, with_mem(ptr));
        })
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        with_alloca(layout, |ptr, uninit: *mut R| {
            ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
            ptr::write(uninit, with_mem(ptr));
        })
    }
}

pub use crate::ffi::stack_alloc as ffi;
