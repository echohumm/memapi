use {
    crate::{
        Alloc,
        Dealloc,
        Grow,
        Layout,
        Realloc,
        Shrink,
        error::AllocError,
        helpers::{null_q_dyn, null_q_zsl_check}
    },
    core::{ffi::c_void, ptr::NonNull},
    ffi::{aligned_alloc, aligned_zalloc, free, grow_aligned, realloc_aligned, shrink_aligned}
};

// TODO: actually consider what attrs fit to match the rest of the crate

#[cfg_attr(miri, track_caller)]
fn pad_then_alloc(
    layout: Layout,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, AllocError> {
    null_q_zsl_check(
        tri!(do layout.to_aligned_alloc_compatible()),
        // SAFETY: we rounded up the layout's values to satisfy the requirements.
        |l| unsafe { alloc(l.align(), l.size()) },
        null_q_dyn
    )
}

#[cfg_attr(miri, track_caller)]
unsafe fn pad_then_grow(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, AllocError> {
    let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
    let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

    null_q_zsl_check(
        new_padded,
        |l| grow_aligned(ptr.as_ptr().cast(), old_padded.size(), l.align(), l.size(), alloc),
        null_q_dyn
    )
}

#[cfg_attr(miri, track_caller)]
unsafe fn pad_then_realloc(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, AllocError> {
    let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
    let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

    null_q_zsl_check(
        new_padded,
        |l| {
            realloc_aligned(
                ptr.as_ptr().cast(),
                old_padded.align(),
                old_padded.size(),
                l.align(),
                l.size(),
                alloc
            )
        },
        null_q_dyn
    )
}

/// An allocator which uses C's `aligned_alloc` set of allocation methods.
///
/// Note that layouts passed to this allocator's allocation methods will have their size and
/// alignment rounded up to meet C's `aligned_alloc` requirements. See
/// [`Layout::to_aligned_alloc_compatible`] for details.
pub struct CAlloc;

impl Alloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        // SAFETY: A
        pad_then_alloc(layout, aligned_alloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        pad_then_alloc(layout, aligned_zalloc)
    }
}
impl Dealloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, _: Layout) {
        free(ptr.as_ptr().cast());
    }
}
impl Grow for CAlloc {
    #[cfg_attr(miri, track_caller)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        if old_layout.size() > new_layout.size() {
            return Err(AllocError::GrowSmallerNewLayout(old_layout.size(), new_layout.size()));
        }

        pad_then_grow(ptr, old_layout, new_layout, aligned_alloc)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        if old_layout.size() > new_layout.size() {
            return Err(AllocError::GrowSmallerNewLayout(old_layout.size(), new_layout.size()));
        }

        pad_then_grow(ptr, old_layout, new_layout, aligned_zalloc)
    }
}
impl Shrink for CAlloc {
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        if old_layout.size() < new_layout.size() {
            return Err(AllocError::ShrinkLargerNewLayout(old_layout.size(), new_layout.size()));
        }

        let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

        null_q_zsl_check(
            new_padded,
            |l| shrink_aligned(ptr.as_ptr().cast(), l.align(), l.size()),
            null_q_dyn
        )
    }
}
impl Realloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        pad_then_realloc(ptr, old_layout, new_layout, aligned_alloc)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        pad_then_realloc(ptr, old_layout, new_layout, aligned_zalloc)
    }
}

/// The C functions and low-level helpers wrapping them which this allocator is based on.
pub mod ffi;
