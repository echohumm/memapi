use {
    crate::{
        error::{Cause, Error},
        ffi::c_alloc::{c_alloc_spec, calloc, free, malloc, rely_on_min_align},
        helpers::null_q_dyn,
        layout::Layout,
        traits::{
            AllocDescriptor,
            alloc::{Alloc, Dealloc, Grow, Realloc, Shrink}
        }
    },
    ::core::{
        cmp::Ord,
        ffi::c_void,
        ops::Fn,
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok}
    },
    ::libc::c_int
};

fn null_q_dyn_or_errcode<F: Fn(Layout) -> (*mut c_void, c_int)>(
    layout: Layout,
    f: F
) -> Result<NonNull<u8>, Error> {
    // _aligned_malloc doesn't have the weird pointer-size requirement
    #[cfg(not(windows))]
    let layout = tri!(::LayoutError layout.to_posix_memalign_compatible());

    assert_unsafe_precondition!(
        noconst, "go tell the developer they're stupid, and a layout somehow became unaligned in \
        CAlloc",
        (layout: Layout = layout) => [layout.align().is_power_of_two()]
    );

    let (ptr, status) = f(layout);
    match status {
        0 => null_q_dyn(ptr, layout),
        code => Err(Error::AllocFailed(layout, Cause::OSErr(code as c_int)))
    }
}

#[cfg_attr(feature = "__dev", allow(rustdoc::broken_intra_doc_links))]
/// An allocator which uses C's allocation functions; [`posix_memalign`](ffi::posix_memalign) on
/// unix and [`_aligned_malloc`](ffi::_aligned_malloc) on Windows.
///
/// Note that layouts passed to this allocator's allocation methods will have their size and
/// alignment rounded up to meet C's [`c_alloc`] requirements. See
/// [`Layout::to_posix_memalign_compatible`] for details.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CAlloc;

impl AllocDescriptor for CAlloc {
    type Error = Error;
}

impl Alloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        null_q_dyn_or_errcode(
            layout,
            // SAFETY: we check the layout is non-zero-sized before use.
            |l| {
                let size = l.size();
                let align = l.align();

                if ffi::rely_on_min_align(size, align) {
                    // SAFETY: requirements are passed on to caller
                    unsafe { (malloc(size), 0) }
                } else {
                    // SAFETY: requirements are passed on to caller
                    unsafe { ffi::c_alloc_spec(align, size) }
                }
            }
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        null_q_dyn_or_errcode(
            layout,
            // SAFETY: we check the layout is non-zero-sized before use.
            |l| {
                let size = l.size();
                let align = l.align();

                if rely_on_min_align(size, align) {
                    // SAFETY: requirements are passed on to caller
                    (unsafe { calloc(1, size) }, 0)
                } else {
                    // SAFETY: requirements are passed on to caller
                    let (ptr, status) = unsafe { c_alloc_spec(align, size) };
                    // zero memory if allocation was successful
                    if !ptr.is_null() {
                        // SAFETY: `ptr` is nonnull, and at least `size` bytes in length.
                        unsafe {
                            ptr::write_bytes(ptr, 0, size);
                        }
                    }
                    (ptr, status)
                }
            }
        )
    }
}
impl Dealloc for CAlloc {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        if ptr != layout.dangling() {
            let padded = tri!(::LayoutError layout.to_posix_memalign_compatible());
            let _size = padded.size();
            let _align = padded.align();

            let ptr = ptr.as_ptr().cast();
            #[cfg(windows)]
            {
                #[allow(clippy::used_underscore_binding)]
                if rely_on_min_align(_size, _align) {
                    // SAFETY: requirements are passed onto the caller; as align <= MIN_ALIGN,
                    // {malloc,calloc} was used so free works.
                    unsafe {
                        free(ptr);
                    }
                } else {
                    // SAFETY: requirements are passed onto the caller; as align > MIN_ALIGN,
                    // _aligned_malloc was used so _aligned_free works.
                    unsafe {
                        ffi::_aligned_free(ptr);
                    }
                }
            }
            #[cfg(not(windows))]
            {
                // SAFETY: requirements are passed on to the caller; free works for all allocation
                //  methods
                unsafe {
                    free(ptr);
                }
            }
        }
        Ok(())
    }
}
impl Grow for CAlloc {}
impl Shrink for CAlloc {}
impl Realloc for CAlloc {}

pub use crate::ffi::c_alloc as ffi;
