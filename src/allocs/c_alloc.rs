use {
    crate::{
        error::{Cause, Error},
        ffi::c_alloc::{c_alloc, c_dealloc, c_zalloc},
        helpers::null_q_dyn,
        layout::Layout,
        traits::{
            AllocError,
            alloc::{Alloc, Dealloc, Grow, Realloc, Shrink}
        }
    },
    ::core::{
        cmp::Ord,
        ffi::c_void,
        ops::Fn,
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    },
    ::cty::c_int
};

fn null_q_dyn_zsl_check_or_errcode<F: Fn(Layout) -> (*mut c_void, c_int)>(
    layout: Layout,
    f: F
) -> Result<NonNull<u8>, Error> {
    if layout.is_zsl() {
        Err(Error::ZeroSizedLayout)
    } else {
        let (ptr, status) = f(layout);
        match status {
            0 => null_q_dyn(ptr, layout),
            code => {
                #[cfg(feature = "os_err_reporting")]
                {
                    Err(Error::AllocFailed(layout, Cause::OSErr(code as c_int)))
                }
                #[cfg(not(feature = "os_err_reporting"))]
                {
                    Err(Error::AllocFailed(layout, Cause::Unknown))
                }
            }
        }
    }
}

#[cfg_attr(feature = "dev", allow(rustdoc::broken_intra_doc_links))]
/// An allocator which uses C's allocation functions; [`posix_memalign`](ffi::posix_memalign) on
/// unix and [`_aligned_malloc`](ffi::_aligned_malloc) on Windows.
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
        null_q_dyn_zsl_check_or_errcode(
            layout,
            // SAFETY: we check the layout is non-zero-sized before use.
            |l| unsafe { c_alloc(l.align(), l.size()) }
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        null_q_dyn_zsl_check_or_errcode(
            layout,
            // SAFETY: we check the layout is non-zero-sized before use.
            |l| unsafe { c_zalloc(l.align(), l.size()) }
        )
    }
}
impl Dealloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        if !layout.is_zsl() && ptr != layout.dangling() {
            let padded = tri!(do layout.to_posix_memalign_compatible());
            c_dealloc(ptr.as_ptr().cast(), padded.align(), padded.size());
        }
        Ok(())
    }
}
impl Grow for CAlloc {}
impl Shrink for CAlloc {}
impl Realloc for CAlloc {}

pub use crate::ffi::c_alloc as ffi;
