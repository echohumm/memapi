#[cfg(feature = "jemalloc")]
/// Module for [jemalloc](https://jemalloc.net/) support.
pub mod jemalloc;

// for the future
#[cfg(feature = "mimalloc")]
/// Module for [mimalloc](https://microsoft.github.io/mimalloc/) support.
pub mod mimalloc;

/// FFI bindings to allocation libraries.
pub mod ffi {
    #[cfg(feature = "jemalloc")]
    /// Bindings from `tikv-jemalloc-sys` and relevant helpers and constants.
    pub mod jem {
        #![allow(unexpected_cfgs)]

        use core::{
            alloc::Layout,
            ffi::{c_int, c_void},
        };

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

        /// Converts a size and alignment to flags in the form of a `c_int`.
        #[inline]
        #[must_use]
        pub fn layout_to_flags(size: usize, align: usize) -> c_int {
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
            malloc_usable_size(ptr.cast())
        }

        #[track_caller]
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

        pub use tikv_jemalloc_sys::*;
    }

    #[cfg(feature = "mimalloc")]
    /// Bindings from `mimalloc-sys`.
    pub mod mim {
        /// Returns the usable size of the allocation pointed to by ptr.
        ///
        /// # Safety
        ///
        /// `ptr` must have been allocated by mimalloc and must not have been freed yet.
        #[inline]
        #[must_use]
        pub unsafe fn usable_size<T>(ptr: *const T) -> usize {
            mi_usable_size(ptr.cast())
        }

        pub use mimalloc_sys::*;
    }
}
