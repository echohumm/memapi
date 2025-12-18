use core::{cmp::Ordering, ffi::c_void, ptr::null_mut};

const NULL: *mut c_void = null_mut();

// TODO: consider must_use and other attrs

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
/// - `align` must be a power of two and a multiple of `size_of::<*mut c_void>()`.
/// - `size` must be a multiple of `align`.
// must be extern "C" to have an fn pointer type compatible with pad_then_alloc
#[allow(clippy::must_use_candidate)]
pub unsafe extern "C" fn aligned_zalloc(align: usize, size: usize) -> *mut c_void {
    // allocate
    // SAFETY: requirements are passed on to the caller.
    let ptr = unsafe { aligned_alloc(align, size) };

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
/// - `old_ptr` must have been allocated by this allocator and be valid for reads of `old_size`
///   bytes.
/// - `old_size` must equal the size of the allocation at `old_ptr`.
/// - `align` must be a power of two and a multiple of `size_of::<*mut c_void>()`.
/// - `size` must be greater than or equal to `old_size` and a multiple of `align`.
#[cfg_attr(miri, track_caller)]
pub unsafe fn grow_aligned(
    old_ptr: *mut c_void,
    old_size: usize,
    align: usize,
    size: usize,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void
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
            free(old_ptr);
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
/// - If `size == 0` the old allocation is freed and `NULL` is returned.
/// - On allocation failure returns `NULL` and does **not** free the original allocation (unless
///   `size == 0`, which already frees).
///
/// # Safety
///
/// - `old_ptr` must have been allocated by this allocator and be valid for reads of at least `size`
///   bytes.
/// - `align` must be a power of two and a multiple of `size_of::<*mut c_void>()`.
/// - `size` must be less than or equal to the size of the allocation at `old_ptr` and a multiple of
///   `align`.
#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink_aligned(
    old_ptr: *mut c_void,
    align: usize,
    size: usize // a memset-ing alloc here is useless, as it will just be overwritten anyways.
) -> *mut c_void {
    // fast path if size is 0, just free and return null
    if size == 0 {
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            free(old_ptr);
        }
        return NULL;
    }

    // allocate new aligned memory
    // SAFETY: requirements are passed on to the caller
    let ptr = unsafe { aligned_alloc(align, size) };

    // if successful, copy data to new pointer, then free old pointer
    if ptr != NULL && old_ptr != NULL {
        // SAFETY: `ptr` and `old_ptr` are nonnull. caller guarantees `size <= old_size`, so copying
        // that many bytes is safe as `ptr` points to an allocation of at least `size` bytes.
        unsafe {
            memcpy(ptr, old_ptr, size);
        }
        // SAFETY: caller guarantees that `old_ptr` is valid
        unsafe {
            free(old_ptr);
        }
    }

    ptr
}

/// Reallocate an allocation to a new size and alignment.
///
/// Behaviour:
/// - If `size > old_size` this grows the allocation (calls [`grow_aligned`]).
/// - If `size < old_size` this shrinks the allocation (calls [`shrink_aligned`]).
/// - If `size == old_size`:
///   - If `align > old_align` a new allocation is performed (as if growing) to satisfy the stricter
///     alignment and the original is freed.
///   - Otherwise the call is a no-op and `old_ptr` is returned unchanged.
///
/// `alloc` is passed only to `grow_aligned`, and ignored if shrinking.
///
/// # Returns
///
/// - On success returns a pointer to an allocation of `size` bytes (may be `old_ptr` if no-op).
/// - On allocation failure returns `NULL` and does **not** free the original allocation except in
///   the `size == 0`/shrink-to-zero case handled by `shrink_aligned`.
///
/// # Safety
///
/// - `old_ptr` must have been allocated by this allocator and be valid for reads of `old_size`
///   bytes (unless `old_ptr` is `NULL` and `old_size == 0`).
/// - `old_size` must match the size of the allocation at `old_ptr`.
/// - `align` must be a power of two and a multiple of `size_of::<*mut c_void>()`.
/// - `size` must be a multiple of `align`.
///
/// # Note
///
/// The `old_align` parameter is only used to determine whether the request can be satisfied in
/// place when `size == old_size`. It being incorrect will not, itself, cause UB, but it may cause
/// the returned pointer to be misaligned.
#[cfg_attr(miri, track_caller)]
pub unsafe fn realloc_aligned(
    old_ptr: *mut c_void,
    old_align: usize,
    old_size: usize,
    align: usize,
    size: usize,
    alloc: unsafe extern "C" fn(usize, usize) -> *mut c_void
) -> *mut c_void {
    match old_size.cmp(&size) {
        // SAFETY: caller guarantees that `old_ptr` and `old_size` are valid, we just checked that
        // `size >= old_size`
        Ordering::Less => unsafe { grow_aligned(old_ptr, old_size, align, size, alloc) },
        Ordering::Equal => {
            if align > old_align {
                // SAFETY: above
                unsafe { grow_aligned(old_ptr, old_size, align, size, alloc) }
            } else {
                old_ptr
            }
        }
        // SAFETY: caller guarantees that `old_ptr` and `size` are valid, we just checked that
        // `size <= old_size`
        Ordering::Greater => unsafe { shrink_aligned(old_ptr, align, size) }
    }
}

extern "C" {
    /// Allocate `size` bytes with at least `align` alignment.
    ///
    /// # Returns
    ///
    /// - On success returns a nonnull pointer to the allocated memory.
    /// - On allocation failure returns `NULL`.
    ///
    /// # Safety
    ///
    /// - `align` must be a power of two and a multiple of `size_of::<*mut c_void>()`.
    /// - `size` must be a multiple of `align`.
    pub fn aligned_alloc(align: usize, size: usize) -> *mut c_void;

    /// Free memory previously returned by `alloc_aligned` (or other allocator helpers here).
    pub fn free(ptr: *mut c_void);

    /// Set `count` bytes at `ptr` to `val`. The returned pointer is a copy of `ptr`.
    pub fn memset(ptr: *mut c_void, val: i32, count: usize) -> *mut c_void;

    /// Copy `count` bytes from `src` to `dest`. The returned pointer is a copy of `dest`.
    pub fn memcpy(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}
