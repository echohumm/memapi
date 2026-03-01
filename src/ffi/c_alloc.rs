#![allow(unknown_lints)]
#![allow(unexpected_cfgs)]
#![warn(unknown_lints)]

use {
    ::core::{ffi::c_void},
    ::libc::c_int
};

#[cfg(any(
    all(target_arch = "riscv32", any(target_os = "espidf", target_os = "zkvm")),
    all(target_arch = "xtensa", target_os = "espidf"),
))]
/// The minimum alignment returned by the platform's [`malloc`].
pub const MIN_ALIGN: usize = 4;

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
/// The minimum alignment returned by the platform's [`malloc`].
pub const MIN_ALIGN: usize = 8;

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
/// The minimum alignment returned by the platform's [`malloc`].
pub const MIN_ALIGN: usize = 16;

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
    any(feature = "dev", test)
))]
compile_error!("this platform is missing a value for `MIN_ALIGN`");

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
    not(any(feature = "dev", test))
))]
// fallback to 1 if not testing
/// The minimum alignment returned by the platform's [`malloc`].
pub const MIN_ALIGN: usize = 1;

#[cfg(all(not(any(target_os = "horizon", target_os = "vita")), not(windows)))]
#[inline(always)]
pub(crate) unsafe fn c_alloc_spec(align: usize, size: usize) -> (*mut c_void, c_int) {
    #[cfg(target_vendor = "apple")]
    {
        if align > (1 << 31) {
            // 22 is the errno for EINVAL
            return (::core::ptr::null_mut(), 22);
        }
    }
    let mut out = ::core::ptr::null_mut();
    // SAFETY: requirements are passed onto the caller
    let ret = unsafe { posix_memalign(&mut out as *mut *mut c_void, align, size) };
    (out, ret)
}
#[cfg(windows)]
#[inline(always)]
pub(crate) unsafe fn c_alloc_spec(align: usize, size: usize) -> (*mut c_void, c_int) {
    // SAFETY: requirements are passed onto the caller
    (unsafe { _aligned_malloc(size, align) }, 0)
}
#[cfg(any(target_os = "horizon", target_os = "vita"))]
#[inline(always)]
pub(crate) unsafe fn c_alloc_spec(layout: &Layout) -> (*mut c_void, c_int) {
    // SAFETY: requirements are passed onto the caller
    (unsafe { memalign(layout.align(), layout.size()) }, 0)
}

#[cfg(windows)]
#[inline(always)]
pub(crate) const fn size_align_check(_: usize, align: usize) -> bool {
    align > MIN_ALIGN
}
#[cfg(not(windows))]
#[inline(always)]
pub(crate) const fn size_align_check(size: usize, align: usize) -> bool {
    align > MIN_ALIGN && size >= align
}

// public in case the user wants them for some reason
extern "C" {
    /// Allocates `size` bytes of uninitialized storage.
    ///
    /// C reference:
    /// <https://en.cppreference.com/w/c/memory/malloc>.
    ///
    /// # Safety
    ///
    /// - Returns a pointer suitably aligned for any object type with fundamental alignment
    ///   (`max_align_t`, at least [`MIN_ALIGN`]).
    /// - On allocation failure, returns `NULL`.
    /// - If `size == 0`, the result is implementation-defined and may be `NULL` or a unique pointer
    ///   that must not be dereferenced but should be freed to avoid memory leaks.
    ///
    /// # Notes
    ///
    /// If successful, the returned pointer should be freed with [`free`].
    #[must_use = "this function allocates memory on success; dropping the returned pointer will \
                  leak memory"]
    pub fn malloc(size: usize) -> *mut c_void;

    /// Allocates storage for an array of `count` objects of `size` bytes each; bytes are
    /// zero-initialized.
    ///
    /// C reference:
    /// <https://en.cppreference.com/w/c/memory/calloc>.
    ///
    /// # Safety
    ///
    /// - Returns a pointer suitably aligned for any object type with fundamental alignment
    ///   (`max_align_t`, at least [`MIN_ALIGN`]).
    /// - On allocation failure, returns `NULL`.
    /// - If `count == 0` or `size == 0`, the result is implementation-defined and may be `NULL` or
    ///   a unique pointer that must not be dereferenced but should be freed to avoid memory leaks.
    ///
    /// # Notes
    ///
    /// If successful, the returned pointer should be freed with [`free`].
    #[must_use = "this function allocates memory on success; dropping the returned pointer will \
                  leak memory"]
    pub fn calloc(count: usize, size: usize) -> *mut c_void;

    /// Changes the size of the memory block pointed to by `ptr` to `size` bytes.
    ///
    /// C reference:
    /// <https://en.cppreference.com/w/c/memory/realloc>.
    ///
    /// # Safety
    ///
    /// - Returns a pointer suitably aligned for any object type with fundamental alignment
    ///   (`max_align_t`, at least [`MIN_ALIGN`]).
    /// - If `ptr` is non-null, it must have been returned by [`malloc`], [`calloc`],
    ///   [`posix_memalign`], or a previous [`realloc`] and must not have been freed.
    /// - If the call fails, it returns `NULL` and the original `ptr` remains valid.
    /// - If `size == 0`, the result is implementation-defined and may be `NULL` or a unique pointer
    ///   that must not be dereferenced but should be freed to avoid memory leaks.
    ///
    /// # Notes
    ///
    /// If successful, the returned pointer should be freed with [`free`].
    #[must_use = "this function allocates memory on success; dropping the returned pointer will \
                  leak memory"]
    pub fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void;

    #[cfg(all(not(windows), not(any(target_os = "horizon", target_os = "vita"))))]
    /// Allocates `size` bytes aligned to `align` and store the result in `*out`.
    ///
    /// POSIX reference:
    /// <https://pubs.opengroup.org/onlinepubs/9699919799/functions/posix_memalign.html>
    ///
    /// # Returns
    ///
    /// - On success returns 0 and stores the pointer in `*out`.
    /// - On error returns an error code, and `*out` is either unmodified or set to `NULL`.
    ///
    /// # Safety
    ///
    /// - On allocation failure, returns `NULL`.
    /// - If `size == 0`, the result is implementation-defined and may be `NULL` or a unique pointer
    ///   that must not be dereferenced but should be freed to avoid memory leaks.
    ///
    /// # Notes
    ///
    /// If successful, the returned pointer should be freed with [`free`].
    #[must_use = "on success this function produces an allocation; dropping the returned value \
                  will leak memory"]
    pub fn posix_memalign(out: *mut *mut c_void, align: usize, size: usize) -> c_int;

    #[cfg(all(not(windows), any(target_os = "horizon", target_os = "vita")))]
    /// Allocates `size` bytes aligned to `align`.
    ///
    /// # Safety
    ///
    /// Platform-dependent. Check platform documentation or assume behavior is similar to
    /// [`posix_memalign`].
    #[must_use = "this function allocates memory on success; dropping the returned pointer will \
                  leak memory"]
    pub fn memalign(align: usize, size: usize) -> *mut c_void;

    /// Frees memory previously returned by the system allocator.
    ///
    /// C reference:
    /// <https://en.cppreference.com/w/c/memory/free>.
    ///
    /// # Safety
    ///
    /// `ptr` must be either `NULL` or a pointer previously returned by [`malloc`], [`calloc`],
    /// [`realloc`], [`posix_memalign`], or another compatible allocator for the platform, and not
    /// yet freed.
    pub fn free(ptr: *mut c_void);

    #[cfg(windows)]
    /// Microsoft version of `aligned_alloc`/[`posix_memalign`]. Allocates `size` bytes aligned to
    /// `align`.
    ///
    /// Microsoft documentation:
    /// <https://learn.microsoft.com/cpp/c-runtime-library/reference/aligned-malloc>.
    ///
    /// # Returns
    ///
    /// - On success returns a non-null pointer.
    /// - On failure or if `size == 0`, returns `NULL`.
    ///
    /// # Safety
    ///
    /// - `align` must be a power of two.
    /// - Memory returned by this function must be freed with [`_aligned_free`], _not_ [`free`].
    #[must_use = "this function allocates memory on success; dropping the returned pointer will \
                  leak memory"]
    pub fn _aligned_malloc(size: usize, align: usize) -> *mut c_void;

    #[cfg(windows)]
    /// Frees memory allocated by `_aligned_malloc`.
    ///
    /// Microsoft documentation:
    /// <https://learn.microsoft.com/cpp/c-runtime-library/reference/aligned-free>.
    ///
    /// # Safety
    ///
    /// `ptr` must be either `NULL` or a pointer previously returned by [`_aligned_malloc`],
    /// [`_aligned_realloc`], or another compatible allocator, and not
    /// yet freed.
    pub fn _aligned_free(ptr: *mut c_void);

    #[cfg(windows)]
    /// Reallocates memory previously returned by [`_aligned_malloc`].
    ///
    /// `align` must match the previous alignment of the allocation, or the call will result in an
    /// error.
    ///
    /// Microsoft documentation:
    /// <https://learn.microsoft.com/cpp/c-runtime-library/reference/aligned-realloc>.
    ///
    /// # Safety
    ///
    /// - `ptr` must have been returned by [`_aligned_malloc`], a previous
    ///   [`_aligned_realloc`]/[`_aligned_recalloc`], or another compatible allocator, and not yet
    ///   freed.
    /// - On failure returns `NULL` and the original pointer remains valid.
    pub fn _aligned_realloc(ptr: *mut c_void, size: usize, align: usize) -> *mut c_void;

    #[cfg(windows)]
    /// Reallocates memory previously returned by [`_aligned_malloc`] and initializes new bytes to
    /// 0.
    ///
    /// `align` must match the previous alignment of the allocation, or the call will result in an
    /// error.
    ///
    /// Microsoft documentation:
    /// <https://learn.microsoft.com/cpp/c-runtime-library/reference/aligned-realloc>.
    ///
    /// # Safety
    ///
    /// - `ptr` must have been returned by [`_aligned_malloc`], a previous
    ///   [`_aligned_realloc`]/[`_aligned_recalloc`], or another compatible allocator, and not yet
    ///   freed.
    /// - On failure returns `NULL` and the original pointer remains valid.
    pub fn _aligned_recalloc(
        ptr: *mut c_void,
        num: usize,
        size: usize,
        align: usize
    ) -> *mut c_void;
}
