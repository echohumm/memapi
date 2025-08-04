#[cfg(feature = "jemalloc")]
/// Module for [jemalloc](https://jemalloc.net/) support.
pub mod jemalloc;

#[cfg(feature = "mimalloc")]
/// Module for [mimalloc](https://microsoft.github.io/mimalloc/) support.
pub mod mimalloc;

#[cfg(any(feature = "jemalloc", feature = "mimalloc"))]
pub(crate) const REALLOC_DIFF_ALIGN: &str =
    "unsupported operation: attempted to reallocate with a different alignment";

#[cfg(any(feature = "jemalloc", feature = "mimalloc"))]
#[cfg_attr(miri, track_caller)]
#[inline]
pub(crate) unsafe fn resize<F: Fn() -> *mut libc::c_void>(
    ralloc: F,
    ptr: core::ptr::NonNull<u8>,
    old_layout: alloc::alloc::Layout,
    new_layout: alloc::alloc::Layout,
    need_same_align: bool,
    is_grow: bool,
) -> Result<core::ptr::NonNull<u8>, crate::error::AllocError> {
    use crate::{error::AllocError, helpers::null_q};

    if need_same_align && new_layout.align() != old_layout.align() {
        return Err(AllocError::Other(REALLOC_DIFF_ALIGN));
    }

    let old_size = old_layout.size();
    let new_size = new_layout.size();

    if new_size == old_size {
        return Ok(ptr);
    } else if is_grow {
        if new_size < old_size {
            return Err(AllocError::GrowSmallerNewLayout(old_size, new_size));
        }
    } else if new_size > old_size {
        return Err(AllocError::ShrinkBiggerNewLayout(old_size, new_size));
    }

    null_q(ralloc(), new_layout)
}

/// FFI bindings to allocation libraries.
pub mod ffi {
    #[cfg(feature = "jemalloc")]
    /// Bindings from `tikv-jemalloc-sys` and relevant helpers and constants.
    pub mod jem {
        #![allow(unexpected_cfgs)]

        use core::alloc::Layout;
        use libc::c_void;

        #[cfg(any(
            target_arch = "arm",
            target_arch = "mips",
            target_arch = "mipsel",
            target_arch = "powerpc"
        ))]
        /// The maximum alignment that the memory allocations returned by the C standard library
        /// memory allocation APIs (e.g. `malloc`) are guaranteed to have.
        pub const ALIGNOF_MAX_ALIGN_T: usize = 8;
        #[cfg(any(
            target_arch = "x86",
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "powerpc64",
            target_arch = "powerpc64le",
            target_arch = "loongarch64",
            target_arch = "mips64",
            target_arch = "riscv64",
            target_arch = "s390x",
            target_arch = "sparc64"
        ))]
        /// The maximum alignment that the memory allocations returned by the C standard library
        /// memory allocation APIs (e.g. `malloc`) are guaranteed to have.
        pub const ALIGNOF_MAX_ALIGN_T: usize = 16;

        #[cfg(feature = "jemalloc")]
        /// Converts a size and alignment to flags in the form of a `c_int`.
        #[inline]
        #[must_use]
        pub fn layout_to_flags(size: usize, align: usize) -> libc::c_int {
            if align <= ALIGNOF_MAX_ALIGN_T && align <= size {
                0
            } else {
                MALLOCX_ALIGN(align)
            }
        }

        /// Returns the usable size of the allocation pointed to by ptr.
        ///
        /// The return value may be larger than the size requested during allocation. This function
        /// is not a mechanism for in-place `realloc()`; rather, it is provided solely as a tool for
        /// introspection purposes. Any discrepancy between the requested allocation size and the
        /// size reported by this function should not be depended on, since such behavior is
        /// entirely implementation-dependent.
        ///
        /// # Safety
        ///
        /// `ptr` must have been allocated by jemalloc and must not have been freed yet.
        #[inline]
        #[must_use]
        pub unsafe fn usable_size<T>(ptr: *const T) -> usize {
            malloc_usable_size(ptr as *const c_void) as usize
        }

        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub(crate) unsafe fn raw_ralloc(
            ptr: *mut c_void,
            old_layout: Layout,
            new_layout: Layout,
        ) -> *mut c_void {
            let flags = layout_to_flags(new_layout.size(), old_layout.align());
            if flags == 0 {
                realloc(ptr, new_layout.size())
            } else {
                rallocx(ptr, new_layout.size(), flags)
            }
        }

        pub use memapi_jemalloc_sys::*;
    }

    #[cfg(feature = "mimalloc")]
    /// Bindings from `mimalloc-sys`.
    pub mod mim {
        use libc::c_void;

        /// Returns the usable size of the allocation pointed to by ptr.
        ///
        /// # Safety
        ///
        /// `ptr` must have been allocated by mimalloc and must not have been freed yet.
        #[inline]
        #[must_use]
        pub unsafe fn usable_size<T>(ptr: *const T) -> usize {
            mi_usable_size(ptr as *const c_void)
        }

        pub use memapi_mimalloc_sys::*;
    }
}
