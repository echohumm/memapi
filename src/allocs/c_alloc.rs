use {
    crate::{
        error::{Cause, Error},
        ffi::c_alloc::{c_alloc, c_dealloc, c_zalloc, grow_aligned, shrink_aligned}
        ,
        layout::Layout,
        traits::{
            alloc::{Alloc, Dealloc, Grow, Realloc, Shrink},
            AllocError
        }
    },
    ::core::{
        cmp::{Ord, Ordering},
        ffi::c_void,
        ops::Fn,
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    },
    ::cty::c_int
};

macro_rules! sz_check {
    ($err:ident, $old:ident $cmp:tt $new:ident) => {
        if $old.size() $cmp $new.size() {
            return Err(Error::$err($old.size(), $new.size()));
        }
    };
}

fn null_q_dyn_zsl_check_or_errcode<F: Fn(Layout) -> (*mut c_void, c_int)>(
    layout: Layout,
    f: F
) -> Result<NonNull<u8>, Error> {
    if layout.is_zero_sized() {
        Err(Error::ZeroSizedLayout)
    } else {
        let (ptr, status) = f(layout);
        if status == -1 {
            // SAFETY: errcode of -1 means it's already been checked and is guaranteed success
            Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
        } else if status == 0 {
            null_q_dyn(ptr, layout)
        } else {
            #[cfg(feature = "os_err_reporting")]
            {
                Err(Error::AllocFailed(layout, Cause::OSErr(status as c_int)))
            }
            #[cfg(not(feature = "os_err_reporting"))]
            {
                Err(Error::AllocFailed(layout, Cause::Unknown))
            }
        }
    }
}

#[cfg_attr(miri, track_caller)]
fn pad_then_alloc(layout: Layout, zeroed: bool) -> Result<NonNull<u8>, Error> {
    let padded = tri!(do layout.to_posix_memalign_compatible());
    let fun = if zeroed { c_zalloc } else { c_alloc };
    // SAFETY: padded layout meets the function's requirements
    null_q_dyn_zsl_check_or_errcode(layout, |_| unsafe { fun(padded.align(), padded.size()) })
}

#[cfg_attr(miri, track_caller)]
unsafe fn pad_then_grow(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    zeroed: bool
) -> Result<NonNull<u8>, Error> {
    sz_check!(GrowSmallerNewLayout, old_layout > new_layout);

    let old_padded = tri!(do old_layout.to_posix_memalign_compatible());
    let new_padded = tri!(do new_layout.to_posix_memalign_compatible());

    null_q_dyn_zsl_check_or_errcode(new_layout, |_| {
        grow_aligned(
            ptr.as_ptr().cast(),
            old_padded.align(),
            old_padded.size(),
            new_padded.align(),
            new_padded.size(),
            zeroed
        )
    })
}

#[cfg_attr(miri, track_caller)]
unsafe fn pad_then_realloc(
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    zeroed: bool
) -> Result<NonNull<u8>, Error> {
    let old_padded = tri!(do old_layout.to_posix_memalign_compatible());
    let new_padded = tri!(do new_layout.to_posix_memalign_compatible());

    null_q_dyn_zsl_check_or_errcode(new_layout, |_| {
        let old_ptr = ptr.as_ptr().cast();
        let old_size = old_padded.size();
        let old_align = old_padded.align();

        let size = new_padded.size();
        let align = new_padded.align();

        match old_size.cmp(&new_padded.size()) {
            // SAFETY: caller guarantees that `old_ptr` and `old_size` are valid, we just
            // checked that `size >= old_size`
            Ordering::Less => unsafe { grow_aligned(old_ptr, old_align, old_size, align, size, zeroed) },
            Ordering::Equal => {
                if align > old_align {
                    // SAFETY: above
                    unsafe { grow_aligned(old_ptr, old_align, old_size, align, size, zeroed) }
                } else {
                    (old_ptr, -1)
                }
            }
            // SAFETY: caller guarantees that `old_ptr` and `size` are valid, we just checked
            // that `size <= old_size`
            Ordering::Greater => unsafe { shrink_aligned(old_ptr, old_align, align, size) }
        }
    })
}

/// An allocator which uses C's [`c_alloc`] set of allocation methods.
///
/// Note that layouts passed to this allocator's allocation methods will have their size and
/// alignment rounded up to meet C's [`c_alloc`] requirements. See
/// [`Layout::to_posix_memalign_compatible`] for details.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CAlloc;

impl AllocError for CAlloc {
    type Error = Error;
}

impl Alloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        pad_then_alloc(layout, false)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        pad_then_alloc(layout, true)
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
            let padded = tri!(do layout.to_posix_memalign_compatible());
            c_dealloc(ptr.as_ptr().cast(), padded.align());
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
        pad_then_grow(ptr, old_layout, new_layout, false)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        pad_then_grow(ptr, old_layout, new_layout, true)
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

        let old_padded = tri!(do old_layout.to_posix_memalign_compatible());
        let new_padded = tri!(do new_layout.to_posix_memalign_compatible());

        null_q_dyn_zsl_check_or_errcode(new_layout, |_| {
            shrink_aligned(ptr.as_ptr().cast(), old_padded.align(), new_padded.align(), new_padded.size())
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
        pad_then_realloc(ptr, old_layout, new_layout, false)
    }
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        pad_then_realloc(ptr, old_layout, new_layout, true)
    }
}

pub use crate::ffi::c_alloc as ffi;
use crate::helpers::null_q_dyn;
