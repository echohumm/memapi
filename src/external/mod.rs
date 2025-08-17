#[cfg(feature = "jemalloc")]
/// Module for [Jemalloc](https://jemalloc.net/) support.
pub mod jemalloc;

#[cfg(feature = "mimalloc")]
/// Module for [`MiMalloc`](https://microsoft.github.io/mimalloc/) support.
pub mod mimalloc;

#[cfg(feature = "malloc")]
/// Module for [libc](https://crates.io/crates/libc) malloc support.
pub mod malloc;

/// FFI bindings to allocation libraries.
pub mod ffi {
    #![allow(unknown_lints, unexpected_cfgs)]

    // It's not my fault if this is wrong, i copied it straight from stdlib (and switched to cfg
    //  attrs from cfg!(), so it's my fault if those are wrong).
    #[cfg(any(
        all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
        all(target_arch = "xtensa", target_os = "espidf"),
    ))]
    /// The maximum alignment that the memory allocations returned by the C standard library
    /// memory allocation APIs (e.g., `malloc`) are guaranteed to have.
    pub const MAX_GUARANTEED_ALIGN: usize = 4;

    //noinspection DuplicatedCode
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
    /// memory allocation APIs (e.g., `malloc`) are guaranteed to have.
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
    /// memory allocation APIs (e.g., `malloc`) are guaranteed to have.
    pub const MAX_GUARANTEED_ALIGN: usize = 16;

    #[cfg(all(
        not(any(
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
        )),
        // we only use this with these features, so don't throw an error if they're not enabled
        not(any(
            feature = "malloc",
            feature = "malloc_defaultalloc",
            feature = "jemalloc"
        ))
    ))]
    compile_error!("MAX_GUARANTEED_ALIGN is needed but not defined for this architecture");

    #[cfg(feature = "jemalloc")]
    /// Bindings from `jemalloc-sys` and relevant helpers and constants.
    pub mod jem {
        #[cfg(feature = "jemalloc")]
        /// Converts a size and alignment to flags in the form of a `c_int`.
        #[must_use]
        pub fn layout_to_flags(size: usize, align: usize) -> libc::c_int {
            if align <= crate::external::ffi::MAX_GUARANTEED_ALIGN && align <= size {
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
    pub mod libc {
        use crate::{
            error::AllocError,
            external::ffi::MAX_GUARANTEED_ALIGN,
            helpers::{null_q_dyn, null_q_zsl_check, preproc_layout},
            Layout,
        };
        use core::ptr::{self, NonNull};

        // making this made me feel bad for the libc devs
        unsafe fn set_errno(err: libc::c_int) {
            #[cfg(any(target_os = "linux", target_os = "fuchsia", target_os = "redox"))]
            {
                ptr::write(libc::__errno_location(), err);
            }
            #[cfg(any(target_os = "android", target_os = "netbsd", target_os = "openbsd"))]
            {
                ptr::write(libc::__errno(), err);
            }
            #[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd"))]
            {
                ptr::write(libc::__error(), err);
            }
            #[cfg(target_os = "illumos")]
            {
                ptr::write(libc::___errno(), err);
            }
        }

        /// Allocates memory.
        #[must_use]
        #[allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
        pub fn alloc_mem(_size: usize, _align: usize) -> *mut u8 {
            #[cfg(all(
                unix,
                not(any(target_os = "tvos", target_os = "visionos", target_os = "watchos"))
            ))]
            unsafe {
                #[cfg(target_vendor = "apple")]
                {
                    if _align > (1 << 31) {
                        return ptr::null_mut();
                    }
                }
                let mut p = ptr::null_mut();
                #[allow(clippy::used_underscore_binding)]
                let res = posix_memalign(&mut p, _align, _size);
                if res != 0 {
                    set_errno(res);
                }
                p.cast()
            }
            #[cfg(windows)]
            unsafe {
                aligned_malloc(_size, _align).cast()
            }
            #[cfg(any(
                not(any(unix, windows)),
                target_os = "tvos",
                target_os = "visionos",
                target_os = "watchos"
            ))]
            {
                compile_error!("unsupported platform");
                ptr::null_mut()
            }
        }

        pub(crate) fn raw_alloc(layout: Layout) -> *mut u8 {
            alloc_mem(layout.size(), layout.align())
        }

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

        pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, layout: Layout) {
            if layout.size() != 0 {
                #[cfg(unix)]
                {
                    free(ptr.cast());
                }
                #[cfg(windows)]
                #[allow(clippy::used_underscore_binding)]
                {
                    aligned_free(ptr.cast());
                }
                #[cfg(not(any(unix, windows)))]
                {
                    compile_error!("unsupported platform");
                }
            }
        }

        pub(crate) unsafe fn raw_realloc(
            ptr: *mut u8,
            _old_layout: Layout,
            new_size: usize,
        ) -> *mut u8 {
            realloc(ptr.cast(), new_size).cast()
        }

        pub(crate) fn alloc(layout: Layout) -> Result<NonNull<u8>, AllocError> {
            null_q_zsl_check(tri!(lay_preproc layout), raw_alloc, null_q_dyn)
        }

        pub(crate) fn zalloc(layout: Layout) -> Result<NonNull<u8>, AllocError> {
            null_q_zsl_check(tri!(lay_preproc layout), raw_zalloc, null_q_dyn)
        }

        pub(crate) unsafe fn dealloc(ptr: NonNull<u8>, layout: Layout) {
            raw_dealloc(
                ptr.as_ptr(),
                match preproc_layout(layout) {
                    Ok(l) => l,
                    Err(e) => panic!("invalid layout: {}", e),
                },
            );
        }

        unsafe fn resize_common(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
            zero_tail: bool,
            use_zalloc_for_new: bool,
            check_size: fn(&usize, &usize) -> bool,
            inv_size_err: fn(usize, usize) -> AllocError,
        ) -> Result<NonNull<u8>, AllocError> {
            let old_size = old_layout.size();
            let new_size = new_layout.size();
            let new_align = new_layout.align();
            let old_align = old_layout.align();

            let same_align = old_align == new_align;

            if same_align && old_size == new_size {
                return Ok(ptr);
            } else if check_size(&old_size, &new_size) {
                return Err(inv_size_err(old_size, new_size));
            } else if same_align || new_align < MAX_GUARANTEED_ALIGN {
                let p = tri!(
                    do null_q_dyn(raw_realloc(ptr.as_ptr(), old_layout, new_size), new_layout)
                );
                if zero_tail && new_size > old_size {
                    ptr::write_bytes(
                        p.as_ptr().add(old_size),
                        0,
                        new_size.saturating_sub(old_size),
                    );
                }
                return Ok(p);
            }

            let new_layout = tri!(lay_preproc new_layout);

            let new_ptr = tri!(do null_q_zsl_check(new_layout, if use_zalloc_for_new {
                raw_zalloc
            } else {
                raw_alloc
            }, null_q_dyn));

            let copy_len = if new_size < old_size {
                new_size
            } else {
                old_size
            };
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), copy_len);

            if zero_tail && new_size > old_size && !use_zalloc_for_new {
                ptr::write_bytes(new_ptr.as_ptr().add(old_size), 0, new_size - old_size);
            }

            dealloc(ptr, old_layout);
            Ok(new_ptr)
        }

        pub(crate) unsafe fn grow(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            resize_common(
                ptr,
                old_layout,
                new_layout,
                false,
                false,
                core::cmp::PartialOrd::gt,
                AllocError::grow_smaller,
            )
        }

        pub(crate) unsafe fn zgrow(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            // zgrow must zero the new bytes. If we must allocate a new block due to alignment,
            // prefer raw_zalloc to get the zeroing for free.
            resize_common(
                ptr,
                old_layout,
                new_layout,
                true,
                true,
                core::cmp::PartialOrd::gt,
                AllocError::grow_smaller,
            )
        }

        pub(crate) unsafe fn shrink(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            resize_common(
                ptr,
                old_layout,
                new_layout,
                false,
                false,
                core::cmp::PartialOrd::lt,
                AllocError::shrink_larger,
            )
        }

        // no size check for realloc
        pub(crate) unsafe fn realloc_helper(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            resize_common(ptr, old_layout, new_layout, false, false, fals, no_err)
        }

        pub(crate) unsafe fn rezalloc(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<u8>, AllocError> {
            resize_common(ptr, old_layout, new_layout, true, false, fals, no_err)
        }

        #[allow(clippy::trivially_copy_pass_by_ref)]
        fn fals(_: &usize, _: &usize) -> bool {
            false
        }
        fn no_err(_: usize, _: usize) -> AllocError {
            // SAFETY: this is unreachable because it's guarded by fals
            unsafe { core::hint::unreachable_unchecked() }
        }

        pub use libc::{calloc, free, malloc, realloc};

        #[cfg(unix)]
        pub use libc::posix_memalign;

        #[cfg(all(target_os = "linux", not(target_env = "ohos")))]
        pub use libc::reallocarray;
        #[cfg(target_os = "linux")]
        pub use libc::{fallocate, fallocate64, memalign, posix_fallocate, posix_fallocate64};
        #[cfg(all(
            target_os = "linux",
            not(any(target_env = "musl", target_env = "ohos"))
        ))]
        pub use libc::{malloc_info, malloc_usable_size};

        #[cfg(windows)]
        pub use libc::{aligned_free, aligned_malloc};
    }
}
