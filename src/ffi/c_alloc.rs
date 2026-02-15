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
pub unsafe fn try_move(ptr: *mut c_void, old_ptr: *mut c_void, size: usize, old_align: usize) {
    if ptr != NULL {
        // SAFETY: `ptr` validated nonnull, caller guarantees `old_ptr` is valid. caller guarantees
        // `size` is <= size of allocation at `ptr` and <= size of allocation at `old_ptr`,
        // so copying that many bytes is safe.
        unsafe {
            memcpy(ptr, old_ptr, size);
        }
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            c_dealloc(old_ptr, old_align);
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
        if layout.align() > (1 << 31) {
            return ptr::null_mut();
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
pub unsafe fn c_dealloc(ptr: *mut c_void, _align: usize) {
    #[cfg(windows)]
    {
        #[allow(clippy::used_underscore_binding)]
        if _align > MIN_ALIGN && size >= align {
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
/// - `align` is a power of two and a multiple of <code>[size_of](::core::mem::size_of)::<*mut
///   [c_void]>()</code>.
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
        try_move(ptr, old_ptr, old_size, old_align);
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
/// - `old_ptr` was allocated by an allocation function listed above and is valid for reads of at
///   least `size` bytes.
/// - `old_align` equals the alignment of the allocation requested at `old_ptr`.
/// - `align` is a power of two and a multiple of <code>[size_of](::core::mem::size_of)::<*mut
///   [c_void]>()</code>.
/// - `size` is less than or equal to the size of the allocation at `old_ptr` and non-zero.
#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink_aligned(
    old_ptr: *mut c_void,
    old_align: usize,
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
        try_move(ptr, old_ptr, size, old_align);
    }

    (ptr, status)
}

// public in case the user wants them for some reason
extern "C" {
    /// Allocates `size` bytes.
    ///
    /// The closest Rust equivalent is [`alloc`](::stdalloc::alloc::alloc) with the `layout`
    /// parameter's alignment being [`MIN_ALIGN`].
    ///
    /// # Safety
    ///
    /// This function is safe to call but may return `NULL` if allocation fails, or `size` is 0.
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn malloc(size: usize) -> *mut c_void;

    /// Allocates `size * count` bytes of zeroed memory.
    ///
    /// The closest Rust equivalent is [`alloc_zeroed`](::stdalloc::alloc::alloc_zeroed) with the
    /// `layout` parameter's size being `count * size` and its alignment being [`MIN_ALIGN`].
    ///
    /// # Safety
    ///
    /// This function is safe to call but may return `NULL` if allocation fails or `size` or `count`
    /// is 0.
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn calloc(count: usize, size: usize) -> *mut c_void;

    /// <placeholder>
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void;

    #[cfg(all(not(windows), not(any(target_os = "horizon", target_os = "vita"))))]
    /// <placeholder>
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn posix_memalign(out: *mut *mut c_void, align: usize, size: usize) -> c_int;

    #[cfg(all(not(windows), any(target_os = "horizon", target_os = "vita")))]
    /// <placeholder>
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn memalign(align: usize, size: usize) -> *mut c_void;

    #[cfg(not(windows))]
    /// Allocates `size` bytes with at least `align` alignment.
    ///
    /// The closest Rust equivalent is [`alloc`](::stdalloc::alloc::alloc).
    ///
    /// # Returns
    ///
    /// - On success returns a nonnull pointer to the allocated memory.
    /// - On allocation failure returns `NULL`.
    ///
    /// # Safety
    ///
    /// This function is safe to call but may return `NULL` if:
    /// - `align` is not a power of two and a multiple of `size_of::<*mut c_void>()`.
    /// - `size` is not a multiple of `align`.
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn aligned_alloc(align: usize, size: usize) -> *mut c_void;

    #[cfg(not(windows))]
    /// Frees memory previously returned by the primary C allocator.
    ///
    /// The closest Rust equivalent is [`dealloc`](::stdalloc::alloc::dealloc).
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to the start of a valid allocation returned by this allocator _or_ is `NULL`.
    /// - `ptr` has not yet been deallocated.
    pub fn free(ptr: *mut c_void);

    #[cfg(windows)]
    /// Windows version of [`aligned_alloc`].
    #[must_use = "this function allocates memory on success, and dropping the returned pointer \
                  will leak memory"]
    pub fn _aligned_malloc(size: usize, alignment: usize) -> *mut c_void;
    #[cfg(windows)]
    /// Windows version of [`free`] specifically for memory returned by [`_aligned_malloc`].
    pub fn _aligned_free(ptr: *mut c_void);
    #[cfg(windows)]
    /// Windows version of [`realloc`] specifically for memory returned by [`_aligned_malloc`].
    pub fn _aligned_realloc(ptr: *mut c_void, size: usize, align: usize) -> *mut c_void;

    /// Sets `count` bytes at `ptr` to `val`. The returned pointer is a copy of `ptr`.
    ///
    /// The closest Rust equivalent is [`write_bytes`](ptr::write_bytes).
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to `count` valid bytes.
    /// - `val` contains a value less than [`u8::MAX`].
    pub fn memset(ptr: *mut c_void, val: i32, count: usize) -> *mut c_void;

    /// Copies `count` bytes from `src` to `dest`. The returned pointer is a copy of `dest`.
    ///
    /// `src` and `dest` must not overlap, or the result stored in `dest` may be unexpected.
    ///
    /// The closest Rust equivalent is [`copy_nonoverlapping`](ptr::copy_nonoverlapping)
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `src` points to a valid block of memory of at least `count` bytes.
    /// - `dest` points to a valid block of memory of at least `count` bytes.
    /// - `src` and `dest` do not overlap.
    pub fn memcpy(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;

    /// Copies `count` bytes from `src` to `dest`. The returned pointer is a copy of `dest`.
    ///
    /// Unlike [`memcpy`], `src` and `dest` may overlap.
    ///
    /// The closest Rust equivalent is [`copy`](ptr::copy)
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `src` points to a valid block of memory of at least `count` bytes.
    /// - `dest` points to a valid block of memory of at least `count` bytes.
    pub fn memmove(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}
