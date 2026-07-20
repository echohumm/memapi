use {
    crate::{
        error::{Cause, Error},
        ffi::c_alloc::{c_alloc_spec, calloc, free, malloc, rely_on_min_align},
        helpers::null_q_dyn,
        layout::Layout,
        traits::{
            AllocDescriptor,
            alloc::{Alloc, Dealloc, Realloc}
        }
    },
    ::core::{
        cmp::Ord,
        ffi::c_void,
        num::NonZeroUsize,
        ops::Fn,
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok}
    },
};

fn null_q_dyn_or_errcode<F: Fn(Layout) -> (*mut c_void, ::libc::c_int)>(
    layout: Layout,
    f: F
) -> Result<NonNull<u8>, Error> {
    if layout.size() == 0 {
        Ok(layout.dangling())
    } else {
        // _aligned_malloc doesn't have the weird pointer-size requirement
        #[cfg(not(windows))]
        let layout = tri!(::LayoutErr layout.to_posix_memalign_compatible());

        let (ptr, status) = f(layout);
        match status {
            0 => null_q_dyn(ptr, layout),
            code => Err(Error::AllocFailed(layout, Cause::OSErr(code as ::libc::c_int)))
        }
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

    #[cfg(any(
        all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
        all(target_arch = "xtensa", target_os = "espidf"),
    ))]
    /// The minimum alignment returned by the platform's [`malloc`].
    // SAFETY: 4 is a non-zero power of two.
    const MIN_ALIGN: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(4) };

    #[cfg(any(
        target_arch = "x86",
        target_arch = "arm",
        target_arch = "m68k",
        target_arch = "csky",
        target_arch = "loongarch32",
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "powerpc",
        target_arch = "powerpc64",
        target_arch = "sparc",
        target_arch = "wasm32",
        target_arch = "hexagon",
        // riscv32 except when handled by the 4-byte case
        all(target_arch = "riscv32", not(any(target_os = "espidf", target_os = "zkvm"))),
        // xtensa except when handled by the 4-byte case
        all(target_arch = "xtensa", not(target_os = "espidf")),
    ))]
    // SAFETY: 8 is a non-zero power of two.
    const MIN_ALIGN: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(8) };

    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm64ec",
        target_arch = "loongarch64",
        target_arch = "mips64",
        target_arch = "mips64r6",
        target_arch = "s390x",
        target_arch = "sparc64",
        target_arch = "riscv64",
        target_arch = "wasm64",
    ))]
    // SAFETY: 16 is a non-zero power of two.
    const MIN_ALIGN: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(16) };

    #[cfg(all(
        not(any(
            all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
            all(target_arch = "xtensa", target_os = "espidf"),
            target_arch = "x86",
            target_arch = "arm",
            target_arch = "m68k",
            target_arch = "csky",
            target_arch = "loongarch32",
            target_arch = "mips",
            target_arch = "mips32r6",
            target_arch = "powerpc",
            target_arch = "powerpc64",
            target_arch = "sparc",
            target_arch = "wasm32",
            target_arch = "hexagon",
            all(target_arch = "riscv32", not(any(target_os = "espidf", target_os = "zkvm"))),
            all(target_arch = "xtensa", not(target_os = "espidf")),
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "arm64ec",
            target_arch = "loongarch64",
            target_arch = "mips64",
            target_arch = "mips64r6",
            target_arch = "s390x",
            target_arch = "sparc64",
            target_arch = "riscv64",
            target_arch = "wasm64",
        )),
        any(feature = "__dev", test)
    ))]
    const MIN_ALIGN: NonZeroUsize =
        compile_error!("this platform is missing a value for `MIN_ALIGN`");
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
        if !layout.is_zsl() && ptr != layout.dangling() {
            let padded = tri!(::LayoutErr layout.to_posix_memalign_compatible());
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
impl Realloc for CAlloc {}

pub use crate::ffi::c_alloc as ffi;
