use {
    crate::{
        error::Error,
        ffi::stack_alloc::with_alloca,
        layout::Layout,
        traits::{AllocDescriptor, AllocFeatures, alloc_temp::AllocTemp}
    },
    ::core::{
        ops::FnOnce,
        ptr::{self, NonNull},
        result::Result
    }
};

pub use crate::ffi::stack_alloc as ffi;
use crate::traits::zst_alloc_temp::ZstAllocTemp;

/// An allocator that uses C's `alloca` for stack allocation.
///
/// This satisfies the requested alignment by allocating extra space and aligning within it. Ensure
/// <code>layout.[size](Layout::size)() + (layout.[align](Layout::align)() - 1)</code> does not
/// exceed the stack limit to avoid overflow.
///
/// # Safety
///
/// The caller must ensure:
/// - attempting to allocate <code>layout.[size](Layout::size)() + (layout.[align](Layout::align)()
///   \- 1)</code> bytes on the stack will not cause a stack overflow.
/// - if compiling with a Rust version below `1.71` and the `catch_unwind` feature is disabled, the
///   `with_mem` function passed to allocation methods will never unwind.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackAlloc;

impl AllocDescriptor for StackAlloc {
    type Error = Error;

    const FEATURES: AllocFeatures = AllocFeatures::empty();
}

// TODO: idk if i like that this is just copy-n-paste of below
impl ZstAllocTemp for StackAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        with_alloca(layout, |ptr, uninit: *mut R| {
            ptr::write(uninit, with_mem(ptr));
        })
    }
}

impl AllocTemp for StackAlloc {
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
}
