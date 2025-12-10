use {
    crate::{
        Alloc,
        Layout,
        data::type_props::{
            PtrProps,
            SizedProps,
            USIZE_MAX_NO_HIGH_BIT,
            varsized_nonnull_from_raw_parts,
            varsized_pointer_from_raw_parts
        },
        error::{AlignErr, AllocError, ArithErr, ArithOp, Cause, InvLayout, LayoutErr}
    },
    core::{
        mem::{forget, transmute},
        num::NonZeroUsize,
        ops::Deref,
        ptr::{self, NonNull}
    }
};

/// Performs a checked arithmetic operation on two `usize`s.
///
/// # Errors
///
/// [`ArithErr`] if the operation would overflow.
pub const fn checked_op(l: usize, op: ArithOp, r: usize) -> Result<usize, ArithErr> {
    let res = match op {
        ArithOp::Add => l.checked_add(r),
        ArithOp::Sub => l.checked_sub(r),
        ArithOp::Mul => l.checked_mul(r),
        ArithOp::Div => l.checked_div(r),
        ArithOp::Rem => l.checked_rem(r),
        // cannot be truncated because we check size first
        #[allow(clippy::cast_possible_truncation)]
        ArithOp::Pow => l.checked_pow(if r > u32::MAX as usize {
            return Err(ArithErr::TooLargeRhs(r));
        } else {
            r as u32
        })
    };

    match res {
        Some(v) => Ok(v),
        None => AllocError::arith_overflow(l, op, r)
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

#[cfg(all(feature = "const_extras", not(feature = "std")))]
/// Performs a checked arithmetic operation on two `usize`s.
///
/// # Panics
///
/// Panics with a generic message if the operation would overflow.
#[allow(unknown_lints)]
#[allow(clippy::incompatible_msrv)]
#[must_use]
pub const fn checked_op_panic_const(l: usize, op: ArithOp, r: usize) -> usize {
    match checked_op(l, op, r) {
        Ok(v) => v,
        Err(_) => panic!("An arithmetic operation overflowed")
    }
}

#[cfg(any(not(feature = "const_extras"), feature = "std"))]
/// Performs a checked arithmetic operation on two `usize`s.
///
/// # Panics
///
/// Panics with a generic message if the operation would overflow.
///
/// If this function isn't const for you, you need to enable the `extra_const` feature.
/// (Raises MSRV to 1.61.0)
#[must_use]
pub fn checked_op_panic_const(l: usize, op: ArithOp, r: usize) -> usize {
    match checked_op(l, op, r) {
        Ok(v) => v,
        Err(..) => panic!("An arithmetic operation overflowed")
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
pub const fn layout_extend(a: Layout, b: Layout) -> Result<(Layout, usize), InvLayout> {
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

/// Returns a [`NonNull`] which has the given alignment as its address.
///
/// # Safety
///
/// Callers must ensure the `alignment` is a valid power of two.
#[must_use]
#[inline]
pub const unsafe fn dangling_nonnull(align: usize) -> NonNull<u8> {
    transmute::<NonZeroUsize, NonNull<u8>>(NonZeroUsize::new_unchecked(align))
}

/// Returns a valid, dangling [`NonNull`] for the given layout.
#[must_use]
pub const fn dangling_nonnull_for(layout: Layout) -> NonNull<u8> {
    // SAFETY: Layout guarantees the alignment is a valid power of 2
    unsafe { dangling_nonnull(layout.align()) }
}

/// Returns the maximum alignment satisfied by a non-null pointer.
#[cfg_attr(miri, track_caller)]
#[must_use]
#[inline]
pub fn ptr_max_align(ptr: NonNull<u8>) -> usize {
    let p = ptr.as_ptr() as usize;
    p & p.wrapping_neg()
}

/// Checks if two pointers of to data of size `sz` overlap.
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

const_if! {
    "const_extras",
    "Creates a `NonNull<[T]>` from a pointer and a length.\n\nThis is a helper used in place of
    [`NonNull::slice_from_raw_parts`], which was stabilized after this crate's MSRV.",
    #[must_use]
    pub const fn nonnull_slice_from_raw_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
        varsized_nonnull_from_raw_parts(p.cast(), len)
    }
}

const_if! {
    "const_extras",
    "Creates a `*mut [T]` from a pointer and a length.\n\nThis is a helper used in place of \
    [`ptr::slice_from_raw_parts_mut`], which was const-stabilized after this crate's MSRV.",
    #[must_use]
    pub const fn slice_ptr_from_raw_parts<T>(p: *mut T, len: usize) -> *mut [T] {
        varsized_pointer_from_raw_parts(p.cast(), len)
    }
}

const_if! {
    "const_max",
    "Returns the length of a [`NonNull`] slice pointer.\n\nThis is a helper used in place of \
    [`NonNull::len`], which was stabilized after this crate's MSRV.\n\n# Safety\n\nCallers must \
    ensure `ptr` is aligned and non-dangling.",
    #[must_use]
    #[inline]
    pub const unsafe fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
        (&*ptr.as_ptr()).len()
    }
}

// Allocation/Result helpers

/// Checks layout for being zero-sized, returning an error if it is, otherwise returning the
/// result of `f(layout)`.
#[cfg_attr(not(feature = "dev"), doc(hidden))]
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
#[cfg_attr(not(feature = "dev"), doc(hidden))]
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
#[cfg_attr(not(feature = "dev"), doc(hidden))]
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
#[cfg_attr(not(feature = "dev"), doc(hidden))]
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    null_q_oserr(ptr, layout)
}

#[cfg(not(feature = "os_err_reporting"))]
/// Calls either [`null_q`] or [`null_q_oserr`] depending on whether `os_err_reporting` is enabled.
///
/// Currently set to call `null_q`.
#[cfg_attr(not(feature = "dev"), doc(hidden))]
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    null_q(ptr, layout)
}

/// Checks layout for being zero-sized, returning an error if it is, otherwise attempting
/// allocation using `f(layout)`.
#[cfg_attr(not(feature = "dev"), doc(hidden))]
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
#[cfg_attr(not(feature = "dev"), doc(hidden))]
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
pub struct AllocGuard<'a, T: ?Sized, A: Alloc + ?Sized> {
    ptr: NonNull<T>,
    alloc: &'a A
}

impl<'a, T: ?Sized, A: Alloc + ?Sized> AllocGuard<'a, T, A> {
    const_if! {
        "const_extras",
        "Creates a new guard from a pointer and a reference to an allocator.\n\n# Safety\n\n\
        Callers must guarantee `ptr` is a valid, readable, writable pointer allocated using \
        `alloc`.",
        #[inline]
        pub const unsafe fn new(ptr: NonNull<T>, alloc: &'a A) -> AllocGuard<'a, T, A> {
            AllocGuard { ptr, alloc }
        }
    }

    const_if! {
        "const_max",
        "Initializes the value by writing to the contained pointer.",
        #[cfg_attr(miri, track_caller)]
        #[inline]
        pub const fn init(&mut self, elem: T)
        where
            T: Sized
        {
            // SAFETY: new() requires that the pointer is safe to write to
            unsafe {
                ptr::write(self.ptr.as_ptr(), elem);
            }
        }
    }

    const_if! {
        "const_extras",
        "Releases ownership of the allocation, preventing deallocation, and returns the raw \
        pointer.",
        #[must_use]
        #[inline]
        pub const fn release(self) -> NonNull<T> {
            let ptr = self.ptr;
            forget(self);
            ptr
        }
    }
}

impl<T: ?Sized, A: Alloc + ?Sized> Drop for AllocGuard<'_, T, A> {
    #[cfg_attr(miri, track_caller)]
    fn drop(&mut self) {
        // SAFETY: new() requires that the pointer was allocated using the provided allocator
        unsafe {
            self.alloc.dealloc(self.ptr.cast::<u8>(), self.ptr.layout());
        }
    }
}

impl<T: ?Sized, A: Alloc + ?Sized> Deref for AllocGuard<'_, T, A> {
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
pub struct SliceAllocGuard<'a, T, A: Alloc + ?Sized> {
    ptr: NonNull<T>,
    alloc: &'a A,
    pub(crate) init: usize,
    full: usize
}

impl<'a, T, A: Alloc + ?Sized> SliceAllocGuard<'a, T, A> {
    const_if! {
        "const_extras",
        "Creates a new slice guard for `full` elements at `ptr` in the given allocator.\n\n# \
        Safety\n\nCallers must ensure that `ptr` was allocated using `alloc`, has space for `full` \
        `T`, and is readable, writable, valid, and aligned.",
        #[inline]
        pub const unsafe fn new(ptr: NonNull<T>, alloc: &'a A, full: usize)
        -> SliceAllocGuard<'a, T, A> {
            SliceAllocGuard {
                ptr,
                alloc,
                init: 0,
                full,
            }
        }
    }

    const_if! {
        "const_extras",
        "Creates a new slice guard for `full` elements at `ptr` in the given allocator.\n\n# \
        Safety\n\nIn addition to the restrictions of [`SliceAllocGuard::new`], callers must ensure \
        that `init` is the number of existing initialized elements in the slice.",
        #[inline]
        pub const unsafe fn new_with_init(ptr: NonNull<T>, alloc: &'a A, init: usize, full: usize)
        -> SliceAllocGuard<'a, T, A> {
            SliceAllocGuard {
                ptr,
                alloc,
                init,
                full,
            }
        }
    }

    const_if! {
        "const_extras",
        "Release ownership of the slice without deallocating memory, returning a `NonNull<T>` \
        pointer to the slice.",
        #[must_use]
        #[inline]
        pub const fn release(self) -> NonNull<[T]> {
            let ret = self.get_init_part();
            forget(self);
            ret
        }
    }

    const_if! {
        "const_extras",
        "Release ownership of the slice without deallocating memory, returning a `NonNull<T>` \
        pointer to the slice's first element.",
        #[must_use]
        #[inline]
        pub const fn release_first(self) -> NonNull<T> {
            let ret = self.ptr;
            forget(self);
            ret
        }
    }

    const_if! {
        "const_extras",
        "Gets a `NonNull<[T]>` pointer to the initialized elements of the slice.",
        #[cfg_attr(miri, track_caller)]
        #[must_use]
        pub const fn get_init_part(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(self.ptr, self.init)
        }
    }

    const_if! {
        "const_extras",
        "Gets a `NonNull<[T]>` pointer to the uninitialized elements of the slice.",
        #[must_use]
        pub const fn get_uninit_part(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(
                // SAFETY: the pointer was a valid NonNull to begin with, adding cannot invalidate
                //  it. `self.init` will be in bounds unless an init-setting method was used
                //  incorrectly.
                unsafe { NonNull::new_unchecked(self.ptr.as_ptr().add(self.init)) },
                self.full - self.init,
            )
        }
    }

    const_if! {
        "const_extras",
        "Gets a `NonNull<[T]>` pointer to the full slice.",
        #[cfg_attr(miri, track_caller)]
        #[must_use]
        pub const fn get_full(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(self.ptr, self.full)
        }
    }

    const_if! {
        "const_max",
        "Sets the initialized element count.\n\n# Safety\n\nCallers must ensure the new \
        count is correct.",
        #[inline]
        pub const unsafe fn set_init(&mut self, init: usize) {
            self.init = init;
        }
    }

    const_if! {
        "const_max",
        "Initializes the next element of the slice with `elem`.\n\n# Errors\n\nReturns \
        `Err(elem)` if the slice is at capacity.",
        #[inline]
        pub const fn init(&mut self, elem: T) -> Result<(), T> {
            if self.init == self.full {
                return Err(elem);
            }
            // SAFETY: we just verified that there is still space for a new element
            unsafe {
                self.init_unchecked(elem);
            }
            Ok(())
        }
    }

    const_if! {
        "const_max",
        "Initializes the next element of the slice with `elem`.\n\n# Safety\n\nCallers must \
        ensure that the slice is not at capacity. (`initialized() < full()`)",
        #[inline]
        pub const unsafe fn init_unchecked(&mut self, elem: T) {
            ptr::write(self.ptr.as_ptr().add(self.init), elem);
            self.init += 1;
        }
    }

    const_if! {
        "const_extras",
        "Returns how many elements have been initialized.",
        #[must_use]
        #[inline]
        pub const fn initialized(&self) -> usize {
            self.init
        }
    }

    const_if! {
        "const_extras",
        "Returns the total number of elements in the slice.",
        #[must_use]
        #[inline]
        pub const fn full(&self) -> usize {
            self.full
        }
    }

    const_if! {
        "const_extras",
        "Returns `true` if every element in the slice has been initialized.",
        #[must_use]
        #[inline]
        pub const fn is_full(&self) -> bool {
            self.init == self.full
        }
    }

    const_if! {
        "const_extras",
        "Returns `true` if no elements have been initialized.",
        #[must_use]
        #[inline]
        pub const fn is_empty(&self) -> bool {
            self.init == 0
        }
    }

    const_if! {
        "const_max",
        "Copies as many elements from `slice` as will fit.\n\nOn success, all elements are \
        copied and `Ok(())` is returned. If `slice.len() > remaining_capacity`, it copies as \
        many elements as will fit, advances the initialized count to full, and returns \
        `Err(excess)`.\n\n# Errors\n\nReturns `Err(excess)` if `slice.len() > \
        remaining_capacity`.",
        pub const fn copy_from_slice(&mut self, slice: &[T]) -> Result<(), usize>
        where
            T: Copy
        {
            let lim = self.full - self.init;
            let to_copy = if slice.len() < lim { slice.len() } else { lim };

            // SAFETY: `self.init` and `to_copy` will disallow oob access unless there was improper
            //  usage of unsafe setter methods
            unsafe {
                ptr::copy(
                    slice.as_ptr(),
                    self.ptr.as_ptr().add(self.init),
                    to_copy
                );
            }

            self.init += to_copy;
            let uncopied = slice.len() - to_copy;
            if uncopied == 0 {
                Ok(())
            } else {
                Err(uncopied)
            }
        }
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
        unsafe {
            for elem in &slice[..to_clone] {
                self.as_ptr().add(self.init).write(elem.clone());
                self.init += 1;
            }
        }

        self.init += to_clone;
        let uncloned = slice.len() - to_clone;
        if uncloned == 0 { Ok(()) } else { Err(uncloned) }
    }

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
                // SAFETY: we just verified that there is space
                Some(elem) => unsafe {
                    ptr::write(self.ptr.as_ptr().add(self.init), elem);
                    self.init += 1;
                },
                None => return Ok(())
            }
        }
    }
}

impl<T, A: Alloc + ?Sized> Drop for SliceAllocGuard<'_, T, A> {
    fn drop(&mut self) {
        // SAFETY: `self.init` will be correct without improper usage of methods which set it. new()
        //  requires that the pointer was allocated using the provided allocator.
        unsafe {
            ptr::drop_in_place(slice_ptr_from_raw_parts(self.ptr.as_ptr(), self.init));
            self.alloc.dealloc(
                self.ptr.cast(),
                Layout::from_size_align_unchecked(T::SZ * self.full, T::ALN)
            );
        }
    }
}

impl<T, A: Alloc + ?Sized> Deref for SliceAllocGuard<'_, T, A> {
    type Target = NonNull<T>;

    #[inline]
    fn deref(&self) -> &NonNull<T> {
        &self.ptr
    }
}
