#[cfg(feature = "jemalloc")]
/// Module for [Jemalloc](https://jemalloc.net/) support.
pub mod jemalloc;

#[cfg(feature = "mimalloc")]
/// Module for [MiMalloc](https://microsoft.github.io/mimalloc/) support.
pub mod mimalloc;

/// FFI bindings to allocation libraries.
pub mod ffi {
    #[cfg(feature = "jemalloc")]
    /// Bindings from `tikv-jemalloc-sys` and relevant helpers and constants.
    pub mod jem {
        #![allow(unknown_lints, unexpected_cfgs)]

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
        #[must_use]
        pub fn layout_to_flags(size: usize, align: usize) -> libc::c_int {
            if align <= ALIGNOF_MAX_ALIGN_T && align <= size {
                0
            } else {
                MALLOCX_ALIGN(align)
            }
        }

        pub use memapi_jemalloc_sys::*;
    }

    #[cfg(feature = "mimalloc")]
    /// Bindings from `mimalloc-sys`.
    pub mod mim {
        pub use memapi_mimalloc_sys::*;
    }
}
