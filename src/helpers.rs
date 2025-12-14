use {
    crate::{
        Alloc,
        BasicAlloc,
        Layout,
        data::type_props::{
            PtrProps,
            SizedProps,
            USIZE_MAX_NO_HIGH_BIT,
            varsized_nonnull_from_parts,
            varsized_ptr_from_parts,
            varsized_ptr_from_parts_mut
        },
        error::{AlignErr, AllocError, ArithErr, ArithOp, Cause, InvLayout, LayoutErr}
    },
    core::{
        mem::forget,
        num::NonZeroUsize,
        ops::Deref,
        ptr::{self, NonNull}
    }
};

// TODO: make const on lower versions
/// Performs a checked arithmetic operation on two `usize`s.
///
/// # Errors
///
/// [`ArithErr`] if the operation would overflow.
#[rustversion::attr(since(1.47), const)]
pub fn checked_op(l: usize, op: ArithOp, r: usize) -> Result<usize, ArithErr> {
    #[rustversion::since(1.52)]
    #[allow(clippy::inline_always)]
    #[inline(always)]
    const fn checked_div(l: usize, r: usize) -> Option<usize> {
        l.checked_div(r)
    }
    #[rustversion::before(1.52)]
    const fn checked_div(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l / r) }
    }

    #[rustversion::since(1.52)]
    #[allow(clippy::inline_always)]
    #[inline(always)]
    const fn checked_rem(l: usize, r: usize) -> Option<usize> {
        l.checked_rem(r)
    }
    #[rustversion::before(1.52)]
    const fn checked_rem(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l % r) }
    }

    #[rustversion::since(1.50)]
    #[allow(clippy::inline_always)]
    #[inline(always)]
    const fn checked_pow(l: usize, r: u32) -> Option<usize> {
        l.checked_pow(r)
    }
    #[rustversion::before(1.50)]
    #[rustversion::attr(since(1.47), const)]
    fn checked_pow(l: usize, mut r: u32) -> Option<usize> {
        if r == 0 {
            return Some(1);
        }
        let mut base = l;
        let mut acc: usize = 1;

        loop {
            if (r & 1) == 1 {
                acc = tri!(opt acc.checked_mul(base));
                // since exp!=0, finally the exp must be 1.
                if r == 1 {
                    return Some(acc);
                }
            }
            r /= 2;
            base = tri!(opt base.checked_mul(base));
        }
    }

    let res = match op {
        // add, sub, and mul use an intrinsic and cannot be manually implemented afaik
        ArithOp::Add => l.checked_add(r),
        ArithOp::Sub => l.checked_sub(r),
        ArithOp::Mul => l.checked_mul(r),
        ArithOp::Div => checked_div(l, r),
        ArithOp::Rem => checked_rem(l, r),
        // cannot be truncated because we check size first
        #[allow(clippy::cast_possible_truncation)]
        ArithOp::Pow => checked_pow(
            l,
            if r > u32::MAX as usize {
                return Err(ArithErr::TooLargeRhs(r));
            } else {
                r as u32
            }
        )
    };

    match res {
        Some(v) => Ok(v),
        None => Err(ArithErr::Overflow(l, op, r))
    }
}

/// Performs a checked arithmetic operation on two `usize`s.
///
/// # Panics
///
/// Panics with information about this function's arguments if the operation would overflow.
#[must_use]
pub fn checked_op_panic(l: usize, op: ArithOp, r: usize) -> usize {
    match checked_op(l, op, r) {
        Ok(v) => v,
        Err(e) => panic!("{}", e)
    }
}

#[rustversion::since(1.57)]
/// Performs a checked arithmetic operation on two `usize`s.
///
/// # Panics
///
/// Panics with a generic message if the operation would overflow.
#[allow(unknown_lints)]
#[must_use]
pub const fn checked_op_panic_const(l: usize, op: ArithOp, r: usize) -> usize {
    match checked_op(l, op, r) {
        Ok(v) => v,
        Err(_) => panic!("an error occurred while performing an arithmetic operation")
    }
}

#[allow(clippy::too_long_first_doc_paragraph)]
/// Given two layouts `a` and `b`, computes a layout describing a block of memory
/// that can hold a value of layout `a` followed by a value of layout `b`, where
/// `b` starts at an offset that satisfies its alignment. Returns the resulting
/// combined layout and the offset at which `b` begins.
///
/// # Errors
///
/// Returns [`InvLayout`] when the resulting size or alignment would exceed
/// [`USIZE_MAX_NO_HIGH_BIT`].
#[rustversion::attr(since(1.47), const)]
pub fn layout_extend(a: Layout, b: Layout) -> Result<(Layout, usize), InvLayout> {
    // compute the offset where `b` would start when placed after `a`, aligned for `b`.
    // SAFETY: `Layout::align()` is always non-zero and a power of two.
    let offset = tri!(do align_up(a.size(), b.align()));

    // i love how max, possibly the simplest function in existence (aside from accessors), is not
    // const.
    let a_align = a.align();
    let b_align = b.align();
    let new_align = if a_align > b_align { a_align } else { b_align };

    // check the total size fits within limits and doesn't overflow.
    match checked_op(a.size(), ArithOp::Add, offset) {
        Ok(total) if total <= USIZE_MAX_NO_HIGH_BIT => {
            // SAFETY: we validated alignment and size constraints above.
            Ok((unsafe { Layout::from_size_align_unchecked(total, new_align) }, offset))
        }
        Err(e) => Err(InvLayout(offset, new_align, LayoutErr::ArithErr(e))),
        _ => Err(InvLayout(offset, new_align, LayoutErr::ExceedsMax))
    }
}

/// Aligns the given value up to a non-zero alignment.
///
/// # Errors
// TODO: better (more specific) docs (doesn't mention LayoutErr or AlignErr type)
/// [`InvLayout`] if either `sz` or `align` are over [`USIZE_MAX_NO_HIGH_BIT`].
pub const fn align_up(sz: usize, align: usize) -> Result<usize, InvLayout> {
    if align == 0 {
        return Err(InvLayout(sz, align, LayoutErr::Align(AlignErr::ZeroAlign)));
    }
    if sz > USIZE_MAX_NO_HIGH_BIT || align > USIZE_MAX_NO_HIGH_BIT {
        return Err(InvLayout(sz, align, LayoutErr::ExceedsMax));
    }

    // SAFETY: align must be nonzero and below the limits.
    Ok(unsafe { align_up_unchecked(sz, align) })
}

/// Aligns the given value up to an alignment.
///
/// # Safety
///
/// `sz` must be no greater than [`USIZE_MAX_NO_HIGH_BIT`].
/// `align` must be non-zero, but no greater than `USIZE_MAX_NO_HIGH_BIT`.
#[must_use]
#[inline]
pub const unsafe fn align_up_unchecked(sz: usize, align: usize) -> usize {
    let m1 = align - 1;
    (sz + m1) & !m1
}

/// Converts a reference into a [`NonNull`].
pub const fn nonnull_from_ref<T: ?Sized>(r: &T) -> NonNull<T> {
    // SAFETY: all references are valid non-null pointers
    unsafe { NonNull::new_unchecked(r as *const T as *mut T) }
}

// TODO: better dangling delegation system, const vers
/// Returns a [`NonNull`] which has the given alignment as its address.
///
/// # Safety
///
/// Callers must ensure the `alignment` is a valid power of two.
#[must_use]
#[inline]
pub const unsafe fn dangling_nonnull(align: usize) -> NonNull<u8> {
    NonNull::new_unchecked(NonZeroUsize::new_unchecked(align).get() as *mut u8)
}

/// Returns a valid, dangling [`NonNull`] for the given layout.
#[must_use]
pub const fn dangling_nonnull_for(layout: Layout) -> NonNull<u8> {
    #[allow(clippy::incompatible_msrv)]
    // SAFETY: Layout guarantees the alignment is a valid power of 2
    unsafe {
        dangling_nonnull(layout.align())
    }
}

/// Returns the maximum alignment satisfied by a non-null pointer.
#[cfg_attr(miri, track_caller)]
#[must_use]
#[inline]
pub fn ptr_max_align(ptr: NonNull<u8>) -> usize {
    let p = ptr.as_ptr() as usize;
    p & p.wrapping_neg()
}

/// Checks if two pointers to data of size `sz` overlap.
#[must_use]
#[inline]
pub fn check_ptr_overlap(a: NonNull<u8>, b: NonNull<u8>, sz: usize) -> bool {
    if sz == 0 {
        return false;
    }

    let a = a.as_ptr() as usize;
    let b = b.as_ptr() as usize;

    if a <= b { (b - a) < sz } else { (a - b) < sz }
}

/// Creates a `NonNull<[T]>` from a pointer and a length.
///
/// This is a helper used in place of
/// [`NonNull::slice_from_raw_parts`], which was stabilized after this crate's MSRV.
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn nonnull_slice_from_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
    varsized_nonnull_from_parts(p.cast(), len)
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// This is a helper used in place of
/// [`ptr::slice_from_raw_parts_mut`], which was const-stabilized after this crate's MSRV.
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn slice_ptr_from_parts_mut<T>(p: *mut T, len: usize) -> *mut [T] {
    varsized_ptr_from_parts_mut(p.cast(), len)
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// This is a helper used in place of
/// [`ptr::slice_from_raw_parts_mut`], which was const-stabilized after this crate's MSRV.
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn slice_ptr_from_parts<T>(p: *const T, len: usize) -> *const [T] {
    varsized_ptr_from_parts(p.cast(), len)
}

/// Returns the length of a [`NonNull`] slice pointer.
///
/// This is a helper used in place of
/// [`NonNull::len`], which was stabilized after this crate's MSRV.
///
/// # Safety
///
/// Callers must ensure `ptr` is aligned and non-dangling.
#[rustversion::attr(since(1.83), const)]
#[must_use]
#[inline]
pub unsafe fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    (&*ptr.as_ptr()).len()
}

// Allocation/Result helpers

/// Checks layout for being zero-sized, returning an error if it is, otherwise returning the
/// result of `f(layout)`.
#[allow(clippy::missing_errors_doc)]
pub fn zsl_check<Ret, F: Fn(Layout) -> Result<Ret, AllocError>>(
    layout: Layout,
    f: F
) -> Result<Ret, AllocError> {
    if layout.size() == 0 {
        Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
    } else {
        f(layout)
    }
}

#[cfg(feature = "os_err_reporting")]
/// Converts a possibly null pointer into a [`NonNull`] result, including os error info.
#[allow(clippy::missing_errors_doc)]
pub fn null_q_oserr<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    if ptr.is_null() {
        Err(AllocError::AllocFailed(
            layout,
            // SAFETY: last_os_error is guaranteed to return a real os error
            Cause::OSErr(unsafe {
                #[allow(clippy::option_if_let_else)]
                match std::io::Error::last_os_error().raw_os_error() {
                    Some(e) => e,
                    None => core::hint::unreachable_unchecked()
                }
            })
        ))
    } else {
        // SAFETY: we just checked that the pointer is non-null
        Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
    }
}

/// Converts a possibly null pointer into a [`NonNull`] result.
#[allow(clippy::missing_errors_doc)]
pub fn null_q<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    if ptr.is_null() {
        Err(AllocError::AllocFailed(layout, Cause::Unknown))
    } else {
        // SAFETY: we just checked that the pointer is non-null
        Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
    }
}

#[cfg(feature = "os_err_reporting")]
/// Calls either [`null_q`] or [`null_q_oserr`] depending on whether `os_err_reporting` is enabled.
///
/// Currently set to call `null_q_oserr`.
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    null_q_oserr(ptr, layout)
}

#[cfg(not(feature = "os_err_reporting"))]
/// Calls either [`null_q`] or [`null_q_oserr`] depending on whether `os_err_reporting` is enabled.
///
/// Currently set to call `null_q`.
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    null_q(ptr, layout)
}

/// Checks layout for being zero-sized, returning an error if it is, otherwise attempting
/// allocation using `f(layout)`.
#[allow(clippy::missing_errors_doc)]
pub fn null_q_zsl_check<T, F: Fn(Layout) -> *mut T>(
    layout: Layout,
    f: F,
    nq: fn(*mut T, Layout) -> Result<NonNull<u8>, AllocError>
) -> Result<NonNull<u8>, AllocError> {
    zsl_check(layout, |layout: Layout| nq(f(layout), layout))
}

/// Allocates memory, then calls a predicate on a pointer to the memory and an extra piece of data.
///
/// This is intended for initializing the memory and/or mapping the success value to another.
#[allow(clippy::missing_errors_doc)]
pub fn alloc_then<Ret, A: Alloc + ?Sized, E, F: Fn(NonNull<u8>, E) -> Ret>(
    a: &A,
    layout: Layout,
    e: E,
    then: F
) -> Result<Ret, AllocError> {
    match a.alloc(layout) {
        Ok(ptr) => Ok(then(ptr, e)),
        Err(e) => Err(e)
    }
}

// TODO: more handling of different rust versions. here, we use proper provenance on versions which
//  need it (>=1.84) by using stdlib's byte_sub when it's available (>=1.75).
#[rustversion::since(1.75)]
/// Subtracts `n` bytes from a pointer's address.
///
/// # Safety
///
/// The caller must ensure:
/// - `n < USIZE_MAX_NO_HIGH_BIT`
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub unsafe fn byte_sub<T: ?Sized>(p: *const T, n: usize) -> *const T {
    p.byte_sub(n)
}
#[rustversion::before(1.75)]
/// Subtracts `n` bytes from a pointer's address.
///
/// # Safety
///
/// The caller must ensure:
/// - `n < USIZE_MAX_NO_HIGH_BIT`
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub unsafe fn byte_sub<T: ?Sized>(p: *const T, n: usize) -> *const T {
    let mut p = p;
    let addr_ptr = (&mut p as *mut *const T).cast::<usize>();
    // SAFETY: the pointer is valid as it is from a &mut.
    unsafe {
        ptr::write(addr_ptr, *addr_ptr - n);
    }
    p
}

#[rustversion::since(1.75)]
/// Adds `n` bytes to a pointer's address.
///
/// # Safety
///
/// The caller must ensure:
/// - `n < USIZE_MAX_NO_HIGH_BIT`
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub unsafe fn byte_add<T: ?Sized>(p: *const T, n: usize) -> *const T {
    p.byte_add(n)
}
#[rustversion::before(1.75)]
/// Adds `n` bytes to a pointer's address.
///
/// # Safety
///
/// The caller must ensure:
/// - `n < USIZE_MAX_NO_HIGH_BIT`
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub unsafe fn byte_add<T: ?Sized>(p: *const T, n: usize) -> *const T {
    let mut p = p;
    let addr_ptr = (&mut p as *mut *const T).cast::<usize>();
    // SAFETY: the pointer is valid as it is from a &mut.
    unsafe {
        ptr::write(addr_ptr, *addr_ptr + n);
    }
    p
}

/// A RAII guard that owns a single allocation and ensures it is deallocated unless explicitly
/// released.
///
/// `AllocGuard` wraps a `NonNull<T>` pointer and an allocator reference `&A`. When the guard
/// goes out of scope, the underlying memory will be deallocated via the allocator.
///
/// To take ownership of the allocation without deallocating, call
/// [`release`](SliceAllocGuard::release), which returns the raw pointer and prevents the guard
/// from running its cleanup.
///
/// This should be used in any situation where the initialization of a pointer's data may panic.
/// (e.g., initializing via a clone or any other user-implemented method)
///
/// # Examples
///
/// ```none
/// # use core::ptr::NonNull;
/// # use memapi2::{helpers::AllocGuard, Alloc, DefaultAlloc};
/// # let alloc = DefaultAlloc;
/// // Allocate space for one `u32` and wrap it in a guard
/// let layout = core::alloc::Layout::new::<u32>();
/// let mut guard = unsafe { AllocGuard::new(alloc.alloc(layout).unwrap().cast::<u32>(), &alloc) };
///
/// // Initialize the value
/// unsafe { guard.as_ptr().write(123) };
///
/// // If everything is OK, take ownership and prevent automatic deallocation
/// // (commented out for this example as the pointer won't be used)
/// // let raw = guard.release();
/// ```
pub struct AllocGuard<'a, T: ?Sized, A: BasicAlloc + ?Sized> {
    /// The pointer this guard will deallocate on panic.
    ptr: NonNull<T>,
    /// The allocator used to allocate/deallocate `ptr`.
    alloc: &'a A
}

impl<'a, T: ?Sized, A: BasicAlloc + ?Sized> AllocGuard<'a, T, A> {
    /// Creates a new guard from a pointer and a reference to an allocator.
    ///
    /// # Safety
    ///
    /// Callers must guarantee `ptr` is a valid, readable, writable pointer allocated using
    /// `alloc`.
    #[rustversion::attr(since(1.61), const)]
    #[inline]
    pub unsafe fn new(ptr: NonNull<T>, alloc: &'a A) -> AllocGuard<'a, T, A> {
        AllocGuard { ptr, alloc }
    }

    /// Initializes the value by writing to the contained pointer.
    #[rustversion::attr(since(1.83), const)]
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn init(&mut self, elem: T)
    where
        T: Sized
    {
        // SAFETY: new() requires that the pointer is safe to write to
        unsafe {
            ptr::write(self.ptr.as_ptr(), elem);
        }
    }

    /// Releases ownership of the allocation, preventing deallocation, and returns the raw
    /// pointer.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn release(self) -> NonNull<T> {
        let ptr = self.ptr;
        forget(self);
        ptr
    }
}

impl<T: ?Sized, A: BasicAlloc + ?Sized> Drop for AllocGuard<'_, T, A> {
    #[cfg_attr(miri, track_caller)]
    fn drop(&mut self) {
        // SAFETY: new() requires that the pointer is valid.
        let layout = unsafe { self.ptr.layout() };
        // SAFETY: new() requires that the pointer was allocated using the provided allocator
        unsafe {
            self.alloc.dealloc(self.ptr.cast::<u8>(), layout);
        }
    }
}

impl<T: ?Sized, A: BasicAlloc + ?Sized> Deref for AllocGuard<'_, T, A> {
    type Target = NonNull<T>;

    #[inline]
    fn deref(&self) -> &NonNull<T> {
        &self.ptr
    }
}

/// A RAII guard for a heap‐allocated slice that tracks how many elements have been initialized.
///
/// On drop, it will:
/// 1. Run destructors for each initialized element.
/// 2. Deallocate the entire slice of memory.
///
/// Use [`init`](SliceAllocGuard::init) or [`init_unchecked`](SliceAllocGuard::init_unchecked)
/// to initialize elements one by one, [`extend_init`](SliceAllocGuard::extend_init) to
/// initialize many elements at once, and [`release`](SliceAllocGuard::release) to take
/// ownership of the fully‐initialized slice without running cleanup.
///
/// # Examples
///
/// ```none
/// # extern crate alloc;
/// # use core::ptr::NonNull;
/// # use memapi2::{
/// #  helpers::SliceAllocGuard,
/// #  Alloc,
/// #  DefaultAlloc,
/// #  data::type_props::SizedProps,
/// #  Layout
/// # };
/// # let alloc = DefaultAlloc;
/// # let len = 5;
///
/// let mut guard = unsafe { SliceAllocGuard::new(
///     alloc.alloc(unsafe { Layout::from_size_align_unchecked(u32::SZ * len, u32::ALN) })
///             .unwrap().cast(),
///     &alloc,
///     len
/// ) };
///
/// for i in 0..len {
///     guard.init(i as u32).unwrap();
/// }
///
/// // All elements are now initialized; take ownership:
/// // (commented out for this example as the pointer won't be used)
/// // let slice_ptr = guard.release();
/// ```
pub struct SliceAllocGuard<'a, T, A: BasicAlloc + ?Sized> {
    /// The pointer to the slice which this guard will deallocate on panic.
    ptr: NonNull<T>,
    /// The allocator used to allocate `ptr`.
    alloc: &'a A,
    /// The initialized element count of the slice.
    pub(crate) init: usize,
    /// The allocated length of the slice.
    full: usize
}

impl<'a, T, A: BasicAlloc + ?Sized> SliceAllocGuard<'a, T, A> {
    /// Creates a new slice guard for `full` elements at `ptr` in the given allocator.
    ///
    /// # Safety
    ///
    /// Callers must ensure that `ptr` was allocated using `alloc`, has space for `full`
    /// `T`, and is readable, writable, valid, and aligned.
    #[rustversion::attr(since(1.61), const)]
    #[inline]
    pub unsafe fn new(ptr: NonNull<T>, alloc: &'a A, full: usize) -> SliceAllocGuard<'a, T, A> {
        SliceAllocGuard { ptr, alloc, init: 0, full }
    }

    /// Creates a new slice guard for `full` elements at `ptr` in the given allocator.
    ///
    /// # Safety
    ///
    /// In addition to the restrictions of [`SliceAllocGuard::new`], callers must ensure
    /// that `init` is the number of existing initialized elements in the slice.
    #[rustversion::attr(since(1.61), const)]
    #[inline]
    pub unsafe fn new_with_init(
        ptr: NonNull<T>,
        alloc: &'a A,
        init: usize,
        full: usize
    ) -> SliceAllocGuard<'a, T, A> {
        SliceAllocGuard { ptr, alloc, init, full }
    }

    /// Release ownership of the slice without deallocating memory, returning a `NonNull<T>`
    /// pointer to the slice.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn release(self) -> NonNull<[T]> {
        let ret = self.get_init_part();
        forget(self);
        ret
    }

    /// Release ownership of the slice without deallocating memory, returning a `NonNull<T>`
    /// pointer to the slice's first element.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn release_first(self) -> NonNull<T> {
        let ret = self.ptr;
        forget(self);
        ret
    }

    /// Gets a `NonNull<[T]>` pointer to the initialized elements of the slice.
    #[rustversion::attr(since(1.61), const)]
    #[cfg_attr(miri, track_caller)]
    #[must_use]
    pub fn get_init_part(&self) -> NonNull<[T]> {
        nonnull_slice_from_parts(self.ptr, self.init)
    }

    /// Gets a `NonNull<[T]>` pointer to the uninitialized elements of the slice.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    pub fn get_uninit_part(&self) -> NonNull<[T]> {
        // SAFETY: `self.init` will be in bounds unless an init-setting method was used incorrectly.
        let ptr = unsafe { self.ptr.as_ptr().add(self.init) };
        nonnull_slice_from_parts(
            // SAFETY: the pointer was a valid NonNull to begin with, adding cannot invalidate
            //  it.
            unsafe { NonNull::new_unchecked(ptr) },
            self.full - self.init
        )
    }

    /// Gets a `NonNull<[T]>` pointer to the full slice.
    #[rustversion::attr(since(1.61), const)]
    #[cfg_attr(miri, track_caller)]
    #[must_use]
    pub fn get_full(&self) -> NonNull<[T]> {
        nonnull_slice_from_parts(self.ptr, self.full)
    }

    /// Sets the initialized element count.
    ///
    /// # Safety
    ///
    /// Callers must ensure the new count is correct.
    #[rustversion::attr(since(1.83), const)]
    #[inline]
    pub unsafe fn set_init(&mut self, init: usize) {
        self.init = init;
    }

    /// Initializes the next element of the slice with `elem`.
    ///
    /// # Errors
    ///
    /// Returns `Err(elem)` if the slice is at capacity.
    #[rustversion::attr(since(1.83), const)]
    #[inline]
    pub fn init(&mut self, elem: T) -> Result<(), T> {
        if self.init == self.full {
            return Err(elem);
        }
        // SAFETY: we just verified that there is still space for a new element
        unsafe {
            self.init_unchecked(elem);
        }
        Ok(())
    }

    /// Initializes the next element of the slice with `elem`.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the slice is not at capacity. (`initialized() < full()`)
    #[rustversion::attr(since(1.83), const)]
    #[inline]
    pub unsafe fn init_unchecked(&mut self, elem: T) {
        ptr::write(self.ptr.as_ptr().add(self.init), elem);
        self.init += 1;
    }

    /// Returns how many elements have been initialized.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn initialized(&self) -> usize {
        self.init
    }

    /// Returns the total number of elements in the slice.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn full(&self) -> usize {
        self.full
    }

    /// Returns `true` if every element in the slice has been initialized.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn is_full(&self) -> bool {
        self.init == self.full
    }

    /// Returns `true` if no elements have been initialized.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.init == 0
    }

    /// Copies as many elements from `slice` as will fit.
    ///
    /// On success, all elements are copied and `Ok(())` is returned. If
    /// `slice.len() > remaining_capacity`, it copies as many elements as will fit, advances the
    /// initialized count to full, and returns `Err(excess)`.
    ///
    /// # Errors
    ///
    /// Returns `Err(excess)` if `slice.len() > remaining_capacity`.
    #[rustversion::attr(since(1.83), const)]
    pub fn copy_from_slice(&mut self, slice: &[T]) -> Result<(), usize>
    where
        T: Copy
    {
        let lim = self.full - self.init;
        let to_copy = if slice.len() < lim { slice.len() } else { lim };

        // SAFETY: `self.init` will be in bounds unless an init-setting method was used incorrectly.
        let uninit_p = unsafe { self.ptr.as_ptr().add(self.init) };

        // SAFETY: to_copy will be at most the remaining space after uninit_p, so it won't go oob.
        unsafe {
            ptr::copy(slice.as_ptr(), uninit_p, to_copy);
        }

        self.init += to_copy;
        let uncopied = slice.len() - to_copy;
        if uncopied == 0 { Ok(()) } else { Err(uncopied) }
    }

    /// Clones as many elements from `slice` as will fit.
    ///
    /// On success, all elements are cloned and `Ok(())` is returned. If
    /// `slice.len() > remaining_capacity`, it clones as many elements as will fit, advances the
    /// initialized count to full, and returns `Err(excess)`.
    ///
    /// # Errors
    ///
    /// `excess` if `slice.len() > remaining_capacity`.
    pub fn clone_from_slice(&mut self, slice: &[T]) -> Result<(), usize>
    where
        T: Clone
    {
        let lim = self.full - self.init;
        let to_clone = if slice.len() < lim { slice.len() } else { lim };

        // SAFETY: `self.init` and `to_clone` will disallow oob access unless there was improper
        //  usage of unsafe setter methods
        for elem in &slice[..to_clone] {
            // SAFETY: `self.init` will be in bounds unless an init-setting method was used
            //  incorrectly.
            let ptr = unsafe { self.as_ptr().add(self.init) };
            // SAFETY: `ptr` is valid. we have not yet incremented `self.init`, so `drop` won't
            //  access uninitialized memory if cloning fails.
            unsafe {
                // TODO: make sure we use ptr::.*(p, args) instead of p\..*(args) everywhere
                ptr::write(ptr, elem.clone());
            }
            self.init += 1;
        }

        self.init += to_clone;
        let uncloned = slice.len() - to_clone;
        if uncloned == 0 { Ok(()) } else { Err(uncloned) }
    }

    // error shows, but it seems to be fine since it compiles
    //noinspection RsAssociatedTypeMismatch
    /// Initializes the next elements of the slice with the elements from `iter`.
    ///
    /// # Errors
    ///
    /// Returns `Err((iter, elem))` if the slice is filled before iteration finishes. The
    /// contained iterator will have been partially consumed.
    pub fn extend_init<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), I::IntoIter> {
        let mut iter = iter.into_iter();
        loop {
            if self.init == self.full {
                return Err(iter);
            }
            match iter.next() {
                Some(elem) => {
                    // SAFETY: we just verified that there is space
                    let uninit_ptr = unsafe { self.ptr.as_ptr().add(self.init) };
                    // SAFETY: the pointer is valid, and we just verified that there is space.
                    unsafe {
                        ptr::write(uninit_ptr, elem);
                        self.init += 1;
                    }
                }
                None => return Ok(())
            }
        }
    }
}

impl<T, A: BasicAlloc + ?Sized> Drop for SliceAllocGuard<'_, T, A> {
    fn drop(&mut self) {
        // SAFETY: `self.init` will be correct without improper usage of methods which set it.
        unsafe {
            ptr::drop_in_place(slice_ptr_from_parts_mut(self.ptr.as_ptr(), self.init));
        }
        // SAFETY: this memory was already allocated with this layout, so its size and align must be
        // valid.
        let layout = unsafe {
            Layout::from_size_align_unchecked(T::SZ * self.full, T::ALN)
        };
        // SAFETY: new() requires that the pointer was allocated using the provided allocator.
        unsafe {
            self.alloc.dealloc(
                self.ptr.cast(),
                layout
            );
        }
    }
}

impl<T, A: BasicAlloc + ?Sized> Deref for SliceAllocGuard<'_, T, A> {
    type Target = NonNull<T>;

    #[inline]
    fn deref(&self) -> &NonNull<T> {
        &self.ptr
    }
}
