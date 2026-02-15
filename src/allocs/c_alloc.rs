use {
    crate::{
        error::Error,
        ffi::c_alloc::{c_alloc, c_dealloc, c_zalloc, grow_aligned, shrink_aligned},
        helpers::null_q_dyn_zsl_check,
        layout::Layout,
        traits::{
            AllocError,
            alloc::{Alloc, Dealloc, Grow, Realloc, Shrink}
        }
    },
    ::core::{
        cmp::{Ord, Ordering},
        ffi::c_void,
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    }
};
// TODO: we should use the builtin malloc and realloc if align <= guaranteed align

macro_rules! sz_check {
    ($err:ident, $old:ident $cmp:tt $new:ident) => {
        if $old.size() $cmp $new.size() {
            return Err(Error::$err($old.size(), $new.size()));
        }
    };
}

#[cfg_attr(miri, track_caller)]
fn pad_then_alloc(
    layout: Layout,
    alloc: unsafe fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, Error> {
    let padded = tri!(do layout.to_aligned_alloc_compatible());
    null_q_dyn_zsl_check(
        layout,
        // SAFETY: we rounded up the layout's values to satisfy the requirements.
        |_| unsafe { alloc(padded.align(), padded.size()) }
    )
}

#[cfg_attr(miri, track_caller)]
unsafe fn pad_then_grow(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    alloc: unsafe fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, Error> {
    sz_check!(GrowSmallerNewLayout, old_layout > new_layout);

    let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
    let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

    null_q_dyn_zsl_check(new_layout, |_| {
        grow_aligned(
            ptr.as_ptr().cast(),
            old_padded.size(),
            new_padded.align(),
            new_padded.size(),
            alloc
        )
    })
}

#[cfg_attr(miri, track_caller)]
unsafe fn pad_then_realloc(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    alloc: unsafe fn(usize, usize) -> *mut c_void
) -> Result<NonNull<u8>, Error> {
    let old_padded = tri!(do old_layout.to_aligned_alloc_compatible());
    let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

    null_q_dyn_zsl_check(new_layout, |_| {
        let old_ptr = ptr.as_ptr().cast();
        let old_size = old_padded.size();
        let old_align = old_padded.align();

        let size = new_padded.size();
        let align = new_padded.align();

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
    })
}

/// An allocator which uses C's [`c_alloc`] set of allocation methods.
///
/// Note that layouts passed to this allocator's allocation methods will have their size and
/// alignment rounded up to meet C's [`c_alloc`] requirements. See
/// [`Layout::to_aligned_alloc_compatible`] for details.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CAlloc;

impl AllocError for CAlloc {
    type Error = Error;
}

impl Alloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        pad_then_alloc(layout, c_alloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        pad_then_alloc(layout, c_zalloc)
    }
}
impl Dealloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        if layout.is_zero_sized() {
            Err(Error::ZeroSizedLayout)
        } else if ptr == layout.dangling() {
            Err(Error::DanglingDeallocation)
        } else {
            c_dealloc(ptr.as_ptr().cast());
            Ok(())
        }
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
        pad_then_grow(ptr, old_layout, new_layout, c_alloc)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        pad_then_grow(ptr, old_layout, new_layout, c_zalloc)
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
        sz_check!(ShrinkLargerNewLayout, old_layout < new_layout);

        let new_padded = tri!(do new_layout.to_aligned_alloc_compatible());

        null_q_dyn_zsl_check(new_layout, |_| {
            shrink_aligned(ptr.as_ptr().cast(), new_padded.align(), new_padded.size())
        })
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
        pad_then_realloc(ptr, old_layout, new_layout, c_alloc)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        pad_then_realloc(ptr, old_layout, new_layout, c_zalloc)
    }
}

pub use crate::ffi::c_alloc as ffi;
