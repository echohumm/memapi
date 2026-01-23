use ::core::{ffi::c_void, ptr::null_mut};

const NULL: *mut c_void = null_mut();

/// Allocates `size` bytes with at least `align` alignment.
///
/// The closest Rust equivalent is [`alloc`](alloc::alloc::alloc).
///
/// # Returns
///
/// - On success returns a nonnull pointer to the allocated memory.
/// - On allocation failure returns `NULL`.
#[must_use = "this function allocates memory on success, and dropping the returned pointer will \
              leak memory"]
pub fn c_alloc(align: usize, size: usize) -> *mut c_void {
    #[cfg(windows)]
    // SAFETY: this function is safe to call
    unsafe {
        _aligned_malloc(size, align)
    }
    #[cfg(not(windows))]
    // SAFETY: this function is safe to call
    unsafe {
        aligned_alloc(align, size)
    }
}

/// Frees memory previously returned by the primary C allocator.
///
/// The closest Rust equivalent is [`dealloc`](alloc::alloc::dealloc).
///
/// # Safety
///
/// The caller must ensure:
/// - `ptr` points to the start of a valid allocation returned by this allocator.
/// - `ptr` has not yet been deallocated.
pub unsafe fn c_dealloc(ptr: *mut c_void) {
    #[cfg(windows)]
    {
        _aligned_free(ptr);
    }
    #[cfg(not(windows))]
    {
        free(ptr);
    }
}

/// Allocate `size` bytes with at least `align` alignment and zero the allocation.
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
/// - `align` is a power of two and a multiple of <code>[size_of]::<*mut [c_void]>()</code>.
/// - `size` is a multiple of `align`.
#[must_use = "this function allocates memory on success, and dropping the returned pointer will \
              leak memory"]
pub unsafe fn aligned_zalloc(align: usize, size: usize) -> *mut c_void {
    // allocate
    // SAFETY: requirements are passed on to the caller.
    let ptr = unsafe { c_alloc(align, size) };

    // zero memory if allocation was successful
    if ptr != NULL {
        // SAFETY: `ptr` is nonnull, and at least size bytes in length. `0i32` fits in a `u8`.
        unsafe {
            memset(ptr, 0, size);
        }
    }

    ptr
}

/// Grow an existing allocation.
///
/// Allocates a new block of `size` bytes with at least `align` alignment, copies `old_size`
/// bytes from `old_ptr` into the new block, frees the old block, and returns the new pointer.
/// New bytes are set by `alloc` and may be uninitialized depending on what allocation function is
/// passed.
///
/// # Returns
///
/// - On success returns a nonnull pointer to the new allocation.
/// - On allocation failure returns `NULL` and does **not** free the original allocation.
///
/// # Safety
///
/// The caller must ensure
/// - `old_ptr` was allocated by this allocator and is valid for reads of `old_size` bytes.
/// - `old_size` equals the size of the allocation requested at `old_ptr`.
/// - `align` is a power of two and a multiple of <code>[size_of]::<*mut [c_void]>()</code>.
/// - `size` is greater than or equal to `old_size` and a multiple of `align`.
#[cfg_attr(miri, track_caller)]
pub unsafe fn grow_aligned(
    old_ptr: *mut c_void,
    old_size: usize,
    align: usize,
    size: usize,
    alloc: unsafe fn(usize, usize) -> *mut c_void
) -> *mut c_void {
    // allocate new aligned memory
    // SAFETY: requirements are passed on to the caller
    let ptr = unsafe { alloc(align, size) };

    // if successful, copy data to new pointer, then free old pointer
    if ptr != NULL && old_ptr != NULL {
        // SAFETY: `ptr` and `old_ptr` are nonnull. caller guarantees `old_size < size`, so copying
        // that  many bytes is safe as `ptr` points to an allocation of at least `size`
        // bytes.
        unsafe {
            memcpy(ptr, old_ptr, old_size);
        }
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            c_dealloc(old_ptr);
        }
    }

    ptr
}

/// Shrink an existing allocation.
///
/// Allocates a new block of `size` bytes with at least `align` alignment, copies `size` bytes
/// from `old_ptr` into the new block, frees the old block, and returns the new pointer.
///
/// # Returns
///
/// - On success returns a nonnull pointer to the new allocation.
/// - If `size == 0`, the old allocation is freed and `NULL` is returned.
/// - On allocation failure returns `NULL` and does **not** free the original allocation (unless
///   `size == 0`, which already frees).
///
/// # Safety
///
/// The caller must ensure:
/// - `old_ptr` was allocated by this allocator and is valid for reads of at least `size` bytes.
/// - `align` is a power of two and a multiple of <code>[size_of]::<*mut [c_void]>()</code>.
/// - `size` is less than or equal to the size of the allocation at `old_ptr` and a multiple of
///   `align`.
#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink_aligned(
    old_ptr: *mut c_void,
    align: usize,
    size: usize // a memset-ing alloc here is useless, as it will just be overwritten anyway.
) -> *mut c_void {
    // fast path if size is 0, just free and return null
    if size == 0 {
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            c_dealloc(old_ptr);
        }
        return NULL;
    }

    // allocate new aligned memory
    // SAFETY: requirements are passed on to the caller
    let ptr = unsafe { c_alloc(align, size) };

    // if successful, copy data to new pointer, then free old pointer
    if ptr != NULL && old_ptr != NULL {
        // SAFETY: `ptr` and `old_ptr` are nonnull. caller guarantees `size <= old_size`, so copying
        // that many bytes is safe as `ptr` points to an allocation of at least `size` bytes.
        unsafe {
            memcpy(ptr, old_ptr, size);
        }
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            c_dealloc(old_ptr);
        }
    }

    ptr
}

// public in case the user wants them for some reason
extern "C" {
    /// Allocates `size` bytes.
    ///
    /// The closest Rust equivalent is [`alloc`](alloc::alloc::alloc) with the layout parameter's
    /// alignment being <code>[align_of]::\<usize\>()</code>
    pub fn malloc(size: usize) -> *mut c_void;

    #[cfg(not(windows))]
    /// Allocates `size` bytes with at least `align` alignment.
    ///
    /// The closest Rust equivalent is [`alloc`](alloc::alloc::alloc).
    ///
    /// # Returns
    ///
    /// - On success returns a nonnull pointer to the allocated memory.
    /// - On allocation failure returns `NULL`.
    ///
    /// # Safety
    ///
    /// This function is safe to call, but may return `NULL` if:
    /// - `align` is not a power of two and a multiple of `size_of::<*mut c_void>()`.
    /// - `size` is not a multiple of `align`.
    pub fn aligned_alloc(align: usize, size: usize) -> *mut c_void;

    #[cfg(not(windows))]
    /// Frees memory previously returned by the primary C allocator.
    ///
    /// The closest Rust equivalent is [`dealloc`](alloc::alloc::dealloc).
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to the start of a valid allocation returned by this allocator
    /// - `ptr` has not yet been deallocated
    pub fn free(ptr: *mut c_void);

    #[cfg(windows)]
    /// Windows version of [`aligned_alloc`]. I don't know the difference and am too lazy to read
    /// Windows docs.
    pub fn _aligned_malloc(size: usize, alignment: usize) -> *mut c_void;
    #[cfg(windows)]
    /// Windows version of [`free`] specifically for memory returned by [`_aligned_malloc`].
    pub fn _aligned_free(ptr: *mut c_void);

    /// Sets `count` bytes at `ptr` to `val`. The returned pointer is a copy of `ptr`.
    ///
    /// The closest Rust equivalent is [`write_bytes`](core::ptr::write_bytes).
    pub fn memset(ptr: *mut c_void, val: i32, count: usize) -> *mut c_void;

    /// Copies `count` bytes from `src` to `dest`. The returned pointer is a copy of `dest`.
    ///
    /// `src` and `dest` may not overlap, or the result stored in `dest` may be unexpected.
    ///
    /// The closest Rust equivalent is [`copy_nonoverlapping`](core::ptr::copy_nonoverlapping)
    pub fn memcpy(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;

    /// Copies `count` bytes from `src` to `dest`. The returned pointer is a copy of `dest`.
    ///
    /// `src` and `dest` may overlap.
    ///
    /// The closest Rust equivalent is [`copy`](core::ptr::copy)
    pub fn memmove(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}
