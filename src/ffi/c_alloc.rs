#![allow(unknown_lints)]
#![allow(unexpected_cfgs)]
#![warn(unknown_lints)]
use {
    ::core::{
        ffi::c_void,
        ptr::{self, null_mut}
    },
    ::cty::c_int
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

const NULL: *mut c_void = null_mut();

/// Copies `size` bytes from `old_ptr` to `ptr` when `ptr` is non-null, then deallocates `old_ptr`.
///
/// If `ptr` is `NULL`, this is a no-op and `old_ptr` is not freed.
///
/// # Safety
///
/// - `old_ptr` must point to a C allocation of at least `size` bytes.
/// - `ptr` must point to an allocation of at least `size` bytes.
pub unsafe fn try_move(
    ptr: *mut c_void,
    old_ptr: *mut c_void,
    copy_count: usize,
    old_align: usize,
    old_size: usize
) {
    if ptr != NULL {
        // SAFETY: `ptr` validated nonnull, caller guarantees `old_ptr` is valid. caller guarantees
        // `size` is <= size of allocation at `ptr` and <= size of allocation at `old_ptr`,
        // so copying that many bytes is safe.
        unsafe {
            ptr::copy_nonoverlapping(old_ptr, ptr, copy_count);
        }
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            c_dealloc(old_ptr, old_align, old_size);
        }
    }
}

/// Allocates `size` bytes with at least `align` alignment.
///
/// The closest Rust equivalent is [`alloc`](::stdalloc::alloc::alloc).
///
/// On non-Windows platforms this forwards to `posix_memalign`, which requires `align` to be a
/// power of two and a multiple of `size_of::<*mut c_void>()`, and `size` to be a multiple of
/// `align`.
///
/// # Returns
///
/// - On success returns a nonnull pointer to the allocated memory.
/// - On allocation failure returns `NULL`.
///
/// # Safety
///
/// The caller must ensure:
/// - `align` is a power of two and a multiple of <code>[size_of](::core::mem::size_of)::<*mut
///   [c_void]>()</code>.
/// - `size` is non-zero.
#[must_use = "this function allocates memory on success, and dropping the returned pointer will \
              leak memory"]
pub unsafe fn c_alloc(align: usize, size: usize) -> (*mut c_void, c_int) {
    if align > MIN_ALIGN && size >= align {
        // SAFETY: requirements are passed on to caller
        unsafe { c_alloc_spec(align, size) }
    } else {
        // SAFETY: requirements are passed on to caller
        unsafe { (malloc(size), 0) }
    }
}

#[cfg(all(not(any(target_os = "horizon", target_os = "vita")), not(windows)))]
#[inline(always)]
unsafe fn c_alloc_spec(align: usize, size: usize) -> (*mut c_void, c_int) {
    #[cfg(target_vendor = "apple")]
    {
        if align > (1 << 31) {
            // 22 is the errno for EINVAL
            return (NULL, 22);
        }
    }
    let mut out = NULL;
    // SAFETY: requirements are passed onto the caller
    let ret = unsafe { posix_memalign(&mut out as *mut *mut c_void, align, size) };
    (out, if ret == 0 { -1 } else { ret })
}
#[cfg(windows)]
#[inline(always)]
unsafe fn c_alloc_spec(align: usize, size: usize) -> (*mut c_void, c_int) {
    // SAFETY: requirements are passed onto the caller
    (unsafe { _aligned_malloc(size, align) }, 0)
}
#[cfg(any(target_os = "horizon", target_os = "vita"))]
#[inline(always)]
unsafe fn c_alloc_spec(layout: &Layout) -> *mut c_void {
    // SAFETY: requirements are passed onto the caller
    (unsafe { memalign(layout.align(), layout.size()) }, 0)
}

/// Allocates `size` bytes with at least `align` alignment and zeroes the allocation.
///
/// # Returns
///
/// - On success returns a nonnull pointer to `size` bytes of memory which are guaranteed to be
///   zeroed.
/// - On allocation failure returns `NULL`.
///
/// # Safety
///
/// The caller must ensure:
/// - `align` is a power of two and a multiple of <code>[size_of](::core::mem::size_of)::<*mut
///   [c_void]>()</code>.
/// - `size` is non-zero.
#[must_use = "this function allocates memory on success, and dropping the returned pointer will \
              leak memory"]
pub unsafe fn c_zalloc(align: usize, size: usize) -> (*mut c_void, c_int) {
    if align > MIN_ALIGN && size >= align {
        // SAFETY: requirements are passed on to caller
        let (ptr, status) = unsafe { c_alloc_spec(align, size) };
        // zero memory if allocation was successful
        if ptr != NULL {
            // SAFETY: `ptr` is nonnull, and at least `size` bytes in length.
            unsafe {
                ptr::write_bytes(ptr, 0, size);
            }
        }
        (ptr, status)
    } else {
        // SAFETY: requirements are passed on to caller
        (unsafe { calloc(1, size) }, 0)
    }
}

/// Frees memory previously returned by [`c_alloc`], [`c_zalloc`], [`c_realloc`], [`malloc`],
/// [`calloc`], [`realloc`], [`grow_aligned`], or [`shrink_aligned`].
///
/// The closest Rust equivalent is [`dealloc`](::stdalloc::alloc::dealloc).
///
/// # Safety
///
/// The caller must ensure:
/// - `ptr` points to the start of a valid allocation returned by an allocation function listed
///   above, or is `NULL`.
/// - `ptr` has not yet been deallocated.
pub unsafe fn c_dealloc(ptr: *mut c_void, _size: usize, _align: usize) {
    #[cfg(windows)]
    {
        #[allow(clippy::used_underscore_binding)]
        if _align > MIN_ALIGN && _size >= _align {
            // SAFETY: requirements are passed onto the caller; as align > MIN_ALIGN,
            // _aligned_{malloc,realloc} was used so _aligned_free works.
            unsafe {
                _aligned_free(ptr);
            }
        } else {
            // SAFETY: requirements are passed onto the caller; as align <= MIN_ALIGN,
            // {malloc,calloc} was used so free works.
            unsafe {
                free(ptr);
            }
        }
    }
    #[cfg(not(windows))]
    {
        // SAFETY: requirements are passed on to the caller; free works for all allocation methods
        unsafe {
            free(ptr);
        }
    }
}

/// Grows a block of memory previously returned by [`c_alloc`], [`c_zalloc`], [`c_realloc`],
/// [`malloc`], [`calloc`], [`realloc`], [`grow_aligned`], or [`shrink_aligned`].
///
/// Allocates a new block of `size` bytes with at least `align` alignment, copies `old_size`
/// bytes from `old_ptr` into the new block, frees the old block, and returns the new pointer. New
/// bytes will be uninitialized if `zeroed` is `false`.
///
/// # Returns
///
/// - On success returns a nonnull pointer to the new allocation.
/// - On allocation failure returns `NULL` and does **not** free the original allocation.
///
/// # Safety
///
/// The caller must ensure:
/// - `old_ptr` was allocated by an allocation function listed above and is valid for reads of
///   `old_size` bytes.
/// - `old_align` equals the alignment of the allocation requested at `old_ptr`.
/// - `old_size` equals the size of the allocation requested at `old_ptr`.
/// - `align` is a power of two and non-zero.
/// - `size` is greater than or equal to `old_size` and non-zero.
#[cfg_attr(miri, track_caller)]
pub unsafe fn grow_aligned(
    old_ptr: *mut c_void,
    old_align: usize,
    old_size: usize,
    align: usize,
    size: usize,
    zeroed: bool
) -> (*mut c_void, c_int) {
    // allocate new aligned memory
    let (ptr, status) =
        // SAFETY: requirements are passed onto the caller
        if zeroed { unsafe { c_zalloc(align, size) } } else { unsafe { c_alloc(align, size) } };
    // TODO: use realloc instead where possible

    // if successful, move data to new pointer
    // SAFETY: requirements are passed on to the caller
    unsafe {
        try_move(ptr, old_ptr, old_size, old_align, old_size);
    }

    (ptr, status)
}


/// Shrinks a block of memory previously returned by [`c_alloc`], [`c_zalloc`], [`c_realloc`],
/// [`malloc`], [`calloc`], [`realloc`], [`grow_aligned`], or [`shrink_aligned`].
///
/// Allocates a new block of `size` bytes with at least `align` alignment, copies `size` bytes
/// from `old_ptr` into the new block, frees the old block, and returns the new pointer.
///
/// # Returns
///
/// - On success returns a nonnull pointer to the new allocation.
/// - On allocation failure returns `NULL` and does __not__ free the original allocation.
///
/// # Safety
///
/// The caller must ensure:
/// - `old_ptr` was allocated by an allocation function listed above and is valid for reads of
///   `size` bytes.
/// - `old_align` equals the alignment of the allocation requested at `old_ptr`.
/// - `old_size` equals the size of the allocation requested at `old_ptr`.
/// - `align` is a power of two and non-zero.
/// - `size` is less than or equal to `old_size` and non-zero.
#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink_aligned(
    old_ptr: *mut c_void,
    old_align: usize,
    old_size: usize,
    align: usize,
    size: usize // a zero here is useless, as it will just be overwritten anyway.
) -> (*mut c_void, c_int) {
    // allocate new aligned memory
    // SAFETY: requirements are passed onto the caller
    let (ptr, status) = unsafe { c_alloc(align, size) };
    // TODO: use realloc

    // if successful, move data to new pointer
    // SAFETY: requirements are passed on to the caller
    unsafe {
        try_move(ptr, old_ptr, size, old_align, old_size);
    }

    (ptr, status)
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
    /// - If `ptr` is non-null, it must have been returned by [`malloc`], [`calloc`].
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

    // TODO: fix these docs
    #[cfg(windows)]
    /// Reallocates memory previously returned by [`_aligned_malloc`] and initializes new bytes to
    /// 0.
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
    pub fn _aligned_recalloc(ptr: *mut c_void, num: usize, size: usize, align: usize) -> *mut c_void;

    /// Set `count` bytes starting at `ptr` to the byte value `val`. Returns `ptr`.
    ///
    /// C reference: <https://en.cppreference.com/w/c/string/byte/memset>.
    ///
    /// # Safety
    ///
    /// - `ptr` must be valid for writes of at least `count` bytes.
    /// - `val` is converted to `unsigned char`/`u8` before being stored.
    pub fn memset(ptr: *mut c_void, val: i32, count: usize) -> *mut c_void;

    /// Copy `count` bytes from `src` to `dest`. The regions must not overlap. Returns `dest`.
    ///
    /// C reference: <https://en.cppreference.com/w/c/string/byte/memcpy>.
    ///
    /// # Safety
    ///
    /// - `src` must be valid for reads of at least `count` bytes.
    /// - `dest` must be valid for writes of at least `count` bytes.
    /// - The source and destination must not overlap.
    pub fn memcpy(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;

    /// Copy `count` bytes from `src` to `dest`. The regions may overlap. Returns `dest`.
    ///
    /// C reference: <https://en.cppreference.com/w/c/string/byte/memmove>.
    ///
    /// # Safety
    ///
    /// - `src` must be valid for reads of at least `count` bytes.
    /// - `dest` must be valid for writes of at least `count` bytes.
    pub fn memmove(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}
