use {
    crate::{
        Alloc,
        Dealloc,
        Grow,
        Layout,
        Realloc,
        Shrink,
        error::Error,
        helpers::{null_q_dyn, null_q_zsl_check}
    },
    core::{ffi::c_void, ptr::NonNull},
    ffi::{aligned_alloc, aligned_zalloc, free, grow_aligned, shrink_aligned},
    std::cmp::Ordering
};

// TODO: switch to posix_memalign? it has clearer requirements than aligned_alloc

// TODO: actually consider what attrs fit to match the rest of the crate

#[cfg_attr(miri, track_caller)]
fn pad_then_alloc(
    layout: Layout,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, Error> {
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
) -> Result<NonNull<u8>, Error> {
    let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
    let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

    if old_padded.size() > new_padded.size() {
        return Err(Error::GrowSmallerNewLayout(old_layout.size(), new_layout.size()));
    }

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
) -> Result<NonNull<u8>, Error> {
    let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
    let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

    null_q_zsl_check(
        new_padded,
        |l| {
            let old_ptr = ptr.as_ptr().cast();
            let old_size = old_padded.size();
            let old_align = old_padded.align();

            let size = l.size();
            let align = l.align();

            match old_size.cmp(&new_padded.size()) {
                // SAFETY: caller guarantees that `old_ptr` and `old_size` are valid, we just
                // checked that `size >= old_size`
                Ordering::Less => unsafe { grow_aligned(old_ptr, old_size, align, size, alloc) },
                Ordering::Equal => {
                    if align > old_align {
                        // SAFETY: above
                        unsafe { grow_aligned(old_ptr, old_size, align, size, alloc) }
                    } else {
                        old_ptr
                    }
                }
                // SAFETY: caller guarantees that `old_ptr` and `size` are valid, we just checked
                // that `size <= old_size`
                Ordering::Greater => unsafe { shrink_aligned(old_ptr, align, size) }
            }
        },
        null_q_dyn
    )
}

/// An allocator which uses C's [`aligned_alloc`] set of allocation methods.
///
/// Note that layouts passed to this allocator's allocation methods will have their size and
/// alignment rounded up to meet C's [`aligned_alloc`] requirements. See
/// [`Layout::to_aligned_alloc_compatible`] for details.
pub struct CAlloc;

impl Alloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        pad_then_alloc(layout, aligned_alloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
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
    ) -> Result<NonNull<u8>, Error> {
        pad_then_grow(ptr, old_layout, new_layout, aligned_alloc)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
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
    ) -> Result<NonNull<u8>, Error> {
        let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
        let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

        if old_padded.size() < new_padded.size() {
            return Err(Error::ShrinkLargerNewLayout(old_layout.size(), new_layout.size()));
        }

        null_q_dyn(
            shrink_aligned(ptr.as_ptr().cast(), new_padded.align(), new_padded.size()),
            new_padded
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
    ) -> Result<NonNull<u8>, Error> {
        pad_then_realloc(ptr, old_layout, new_layout, aligned_alloc)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        pad_then_realloc(ptr, old_layout, new_layout, aligned_zalloc)
    }
}

/// The C functions and low-level helpers wrapping them which this allocator is based on.
pub mod ffi;
