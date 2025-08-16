// TODO: dedup these, particularly the null return handling logic
#[cfg(feature = "jemalloc")]
/// Module for [Jemalloc](https://jemalloc.net/) support.
pub mod jemalloc;

#[cfg(feature = "mimalloc")]
/// Module for [`MiMalloc`](https://microsoft.github.io/mimalloc/) support.
pub mod mimalloc;

#[cfg(feature = "malloc")]
/// Module for [libc](https://crates.io/crates/libc) malloc support.
pub mod libc_malloc;

/// FFI bindings to allocation libraries.
pub mod ffi {
    /// The maximum alignment that the memory allocations returned by the C standard library
    /// memory allocation APIs (e.g. `malloc`) are guaranteed to have.
    // It's not my fault if this is wrong, i copied it straight from stdlib (and switched to cfg
    //  attrs from cfg!(), so it is my fault if those are wrong).
    #[cfg(any(
        all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
        all(target_arch = "xtensa", target_os = "espidf"),
    ))]
    pub const MAX_GUARANTEED_ALIGN: usize = 4;

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
        target_arch = "riscv32",
        target_arch = "xtensa",
    ))]
    #[cfg(not(any(
        all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
        all(target_arch = "xtensa", target_os = "espidf"),
    )))]
    /// The maximum alignment that the memory allocations returned by the C standard library
    /// memory allocation APIs (e.g. `malloc`) are guaranteed to have.
    pub const MAX_GUARANTEED_ALIGN: usize = 8;

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
    /// The maximum alignment that the memory allocations returned by the C standard library
    /// memory allocation APIs (e.g. `malloc`) are guaranteed to have.
    pub const MAX_GUARANTEED_ALIGN: usize = 16;

    #[cfg(not(any(
        any(
            all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
            all(target_arch = "xtensa", target_os = "espidf"),
        ),
        any(
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
            target_arch = "riscv32",
            target_arch = "xtensa",
        ),
        any(
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
        ),
    )))]
    compile_error!("add a value for ALIGNOF_MAX_ALIGN_T");

    #[cfg(feature = "jemalloc")]
    /// Bindings from `jemalloc-sys` and relevant helpers and constants.
    pub mod jem {
        #![allow(unknown_lints, unexpected_cfgs)]

        #[cfg(feature = "jemalloc")]
        /// Converts a size and alignment to flags in the form of a `c_int`.
        #[must_use]
        pub fn layout_to_flags(size: usize, align: usize) -> libc::c_int {
            if align <= crate::ffi::MAX_GUARANTEED_ALIGN && align <= size {
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

    #[cfg(any(feature = "malloc", feature = "malloc_defaultalloc"))]
    #[allow(clippy::module_name_repetitions)]
    /// Bindings to `libc`'s allocation functions and small helpers.
    // TODO: make this less GARBAGE. I HATE THIS MORE THAN MANUALLY TRANSMUTING (*mut T, usize) TO
    //  *mut [T].
    pub mod malloc {
        use crate::{
            error::AllocError,
            ffi::MAX_GUARANTEED_ALIGN,
            helpers::{null_q_dyn, null_q_zsl_check},
            Layout,
        };
        use core::ptr::{self, NonNull};

        /// Allocates memory.
        #[cfg_attr(miri, track_caller)]
        #[must_use]
        #[allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
        pub fn alloc_mem(size: usize, align: usize) -> *mut u8 {
            #[cfg(unix)]
            unsafe {
                #[cfg(target_vendor = "apple")]
                {
                    if align > (1 << 31) {
                        return core::ptr::null_mut();
                    }
                }
                memalign(size, align).cast()
            }
            #[cfg(windows)]
            unsafe {
                aligned_malloc(size, align).cast()
            }
            // TODO: other platforms
            #[cfg(not(any(unix, windows)))]
            {
                compile_error!("unsupported platform");
            }
        }

        /// Frees allocated memory. The inverse of [`alloc_mem`].
        ///
        /// # Safety
        ///
        /// `ptr` must:
        /// - point to a block of memory allocated via this allocator
        /// - have been allocated with an alignment of `_align`
        #[cfg_attr(miri, track_caller)]
        pub unsafe fn free_mem(ptr: *mut u8, _align: usize) {
            #[cfg(unix)]
            {
                free(ptr.cast());
            }
            #[cfg(windows)]
            #[allow(clippy::used_underscore_binding)]
            {
                aligned_free(ptr.cast(), _align);
            }
            #[cfg(not(any(unix, windows)))]
            {
                compile_error!("unsupported platform");
            }
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) fn raw_alloc(layout: Layout) -> *mut u8 {
            alloc_mem(layout.size(), layout.align())
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) fn raw_zalloc(layout: Layout) -> *mut u8 {
            let size = layout.size();
            let align = layout.align();

            // SAFETY: `calloc` is safe, we check the pointer is valid before writing to it.
            unsafe {
                if align <= MAX_GUARANTEED_ALIGN {
                    calloc(1, size).cast()
                } else {
                    let p = alloc_mem(size, align);
                    if !p.is_null() {
                        ptr::write_bytes(p, 0, size);
                    }
                    p
                }
            }
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, layout: Layout) {
            if layout.size() != 0 {
                free_mem(ptr, layout.align());
            }
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn raw_realloc(
            ptr: *mut u8,
            _old_layout: Layout,
            new_size: usize,
        ) -> *mut u8 {
            realloc(ptr.cast(), new_size).cast()
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) fn alloc(layout: Layout) -> Result<NonNull<u8>, AllocError> {
            null_q_zsl_check(layout, raw_alloc, null_q_dyn)
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) fn zalloc(layout: Layout) -> Result<NonNull<u8>, AllocError> {
            null_q_zsl_check(layout, raw_zalloc, null_q_dyn)
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn dealloc(ptr: NonNull<u8>, layout: Layout) {
            raw_dealloc(ptr.as_ptr(), layout);
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn grow(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            let old_size = old_layout.size();
            let new_size = new_layout.size();
            let new_align = new_layout.align();

            // TODO: dedup this with shrink()/realloc_helper()
            if new_size == old_size && new_align == old_layout.align() {
                return Ok(ptr);
            } else if new_size < old_size {
                return Err(AllocError::GrowSmallerNewLayout(old_size, new_size));
            }

            // path for same alignment (just realloc)
            if new_align == old_layout.align() || new_align < MAX_GUARANTEED_ALIGN {
                return null_q_dyn(raw_realloc(ptr.as_ptr(), old_layout, new_size), new_layout);
            }

            // path for different alignment (allocate new memory and copy data)
            let new_ptr = tri!(do null_q_zsl_check(new_layout, raw_alloc, null_q_dyn));
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
            dealloc(ptr, old_layout);
            Ok(new_ptr)
        }

        pub(crate) unsafe fn zgrow(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            let old_size = old_layout.size();
            let new_size = new_layout.size();
            let new_align = new_layout.align();
            let old_align = old_layout.align();

            if new_size == old_size && new_align == old_align {
                return Ok(ptr);
            } else if new_size < old_size {
                return Err(AllocError::GrowSmallerNewLayout(old_size, new_size));
            }

            // if alignment is unchanged or small enough for libc guarantees, we can realloc
            // then zero only the extended part.
            if new_align == old_align || new_align < MAX_GUARANTEED_ALIGN {
                // Attempt realloc
                let p = null_q_dyn(raw_realloc(ptr.as_ptr(), old_layout, new_size), new_layout)?;
                // Zero only the newly allocated tail
                let tail = new_size.saturating_sub(old_size);
                if tail > 0 {
                    ptr::write_bytes(p.as_ptr().add(old_size), 0, tail);
                }
                return Ok(p);
            }

            // for diff/large alignment we need to manually realloc
            let new_ptr = tri!(do null_q_zsl_check(new_layout, raw_zalloc, null_q_dyn));
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
            dealloc(ptr, old_layout);
            Ok(new_ptr)
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn shrink(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            let old_size = old_layout.size();
            let new_size = new_layout.size();
            let new_align = new_layout.align();
            let old_align = old_layout.align();

            if new_size == old_size && new_align == old_align {
                return Ok(ptr);
            } else if new_size > old_size {
                return Err(AllocError::ShrinkBiggerNewLayout(old_size, new_size));
            }

            if new_align == old_align || new_align < MAX_GUARANTEED_ALIGN {
                return null_q_dyn(raw_realloc(ptr.as_ptr(), old_layout, new_size), new_layout);
            }

            let new_ptr = tri!(do null_q_zsl_check(new_layout, raw_alloc, null_q_dyn));
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_size);
            dealloc(ptr, old_layout);
            Ok(new_ptr)
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn realloc_helper(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            let old_size = old_layout.size();
            let new_size = new_layout.size();
            let new_align = new_layout.align();
            let old_align = old_layout.align();

            if new_size == old_size && new_align == old_align {
                return Ok(ptr);
            }

            if new_align == old_align || new_align < MAX_GUARANTEED_ALIGN {
                return null_q_dyn(raw_realloc(ptr.as_ptr(), old_layout, new_size), new_layout);
            }

            let new_ptr = tri!(do null_q_zsl_check(new_layout, raw_alloc, null_q_dyn));
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_size);
            dealloc(ptr, old_layout);
            Ok(new_ptr)
        }

        #[cfg_attr(miri, track_caller)]
        pub(crate) unsafe fn rezalloc(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            if new_layout.size() > old_layout.size() {
                zgrow(ptr, old_layout, new_layout)
            } else {
                shrink(ptr, old_layout, new_layout)
            }
        }

        pub use libc::{calloc, free, malloc, realloc};

        // TODO: make sure all compat ones are above, not behind this cfg
        #[cfg(unix)]
        pub use libc::{
            fallocate, fallocate64, malloc_info, malloc_usable_size, memalign, posix_fallocate,
            posix_fallocate64, posix_memalign, reallocarray,
        };

        #[cfg(windows)]
        pub use libc::{aligned_free, aligned_malloc};
    }
}
