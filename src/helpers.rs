use crate::{
    error::AllocError,
    type_props::{PtrProps, SizedProps, USIZE_MAX_NO_HIGH_BIT},
    Alloc,
};
use core::{
    alloc::Layout,
    mem::{forget, transmute},
    num::NonZeroUsize,
    ops::Deref,
    ptr::{self, eq as peq, NonNull},
};

#[cfg(any(feature = "alloc_slice", feature = "alloc_ext"))]
/// Allocates memory, then calls a predicate on a pointer to the memory and an extra piece of data.
pub(crate) fn alloc_then<Ret, A: Alloc + ?Sized, E, F: Fn(NonNull<u8>, E) -> Ret>(
    a: &A,
    layout: Layout,
    e: E,
    then: F,
) -> Result<Ret, AllocError> {
    match a.alloc(layout) {
        Ok(ptr) => Ok(then(ptr, e)),
        Err(e) => Err(e),
    }
}

/// Creates a `NonNull<[T]>` from a pointer and a length.
///
/// This is a helper used in place of [`NonNull::slice_from_raw_parts`], which was stabilized
/// after this crate's MSRV.
#[must_use]
pub const fn nonnull_slice_from_raw_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
    unsafe { NonNull::new_unchecked(slice_ptr_from_raw_parts(p.as_ptr(), len)) }
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// This is a helper used in place of [`ptr::slice_from_raw_parts_mut`], which was
/// const-stabilized after this crate's MSRV.
///
#[doc = "## Small disclaimer: you must guarantee this function will work, as Rust's fat \
    pointers changing layout would result in this function causing UB."]
#[must_use]
pub const fn slice_ptr_from_raw_parts<T>(p: *mut T, len: usize) -> *mut [T] {
    unsafe { transmute::<(*mut T, usize), *mut [T]>((p, len)) }
}

const_if! {
    "extra_extra_const",
    "Returns the length of a [`NonNull`] slice pointer.\n\nThis is a helper used in place of \
    [`NonNull::len`], which was stabilized after this crate's MSRV.",
    #[must_use]
    pub const fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
        unsafe { (&*ptr.as_ptr()).len() }
    }
}

/// Checks layout for being zero-sized, returning an error if it is, otherwise attempting
/// allocation using `f(layout)`.
pub(crate) fn null_q_zsl_check<T, F: Fn(Layout) -> *mut T>(
    layout: Layout,
    f: F,
) -> Result<NonNull<u8>, AllocError> {
    zsl_check(layout, |layout: Layout| {
        null_q(f(layout).cast::<u8>(), layout)
    })
}

/// Converts a possibly null pointer into a [`NonNull`] result.
pub(crate) fn null_q<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    if ptr.is_null() {
        Err(AllocError::AllocFailed(layout))
    } else {
        Ok(unsafe { NonNull::new_unchecked(ptr.cast::<u8>()) })
    }
}

/// Checks layout for being zero-sized, returning an error if it is, otherwise returning the
/// result of `f(layout)`.
pub(crate) fn zsl_check<Ret, F: Fn(Layout) -> Result<Ret, AllocError>>(
    layout: Layout,
    f: F,
) -> Result<Ret, AllocError> {
    if layout.size() == 0 {
        Err(AllocError::ZeroSizedLayout(dangling_nonnull_for(layout)))
    } else {
        f(layout)
    }
}

/// Checks equality between two [`NonNull`] pointers.
#[must_use]
pub fn nonnull_eq<T: ?Sized>(a: NonNull<T>, b: NonNull<T>) -> bool {
    peq(a.as_ptr() as *const T, b.as_ptr() as *const T)
}

/// Aligns the given value up to a non-zero alignment.
#[must_use]
pub const fn align_up(n: usize, align: NonZeroUsize) -> usize {
    unsafe { align_up_unchecked(n, align.get()) }
}

/// Aligns the given value up to an alignment.
///
/// # Safety
///
/// `align` must be non-zero.
#[must_use]
pub const unsafe fn align_up_unchecked(n: usize, align: usize) -> usize {
    let m1 = align - 1;
    (n + m1) & !m1
}

/// Returns a valid, dangling [`NonNull`] for the given layout.
#[must_use]
pub const fn dangling_nonnull_for(layout: Layout) -> NonNull<u8> {
    unsafe { dangling_nonnull(layout.align()) }
}

/// Returns a [`NonNull`] which has the given alignment as its address.
///
/// # Safety
///
/// The caller must ensure the `alignment` is a valid power of two.
#[must_use]
pub const unsafe fn dangling_nonnull(align: usize) -> NonNull<u8> {
    transmute::<NonZeroUsize, NonNull<u8>>(NonZeroUsize::new_unchecked(align))
}

// here only because it may be used elsewhere later
#[cfg(feature = "alloc_slice")]
/// Gets either a valid layout with space for `n` count of `T`, or an 
/// `AllocError::LayoutError(sz, aln)`.
pub(crate) const fn layout_or_err<T>(n: usize) -> Result<Layout, AllocError> {
    match layout_or_sz_align::<T>(n) {
        Ok(l) => Ok(l),
        Err((sz, aln)) => Err(AllocError::InvalidLayout(sz, aln))
    }
}

/// Gets either a valid layout with space for `n` count of `T`, or a raw size and alignment.
///
/// # Errors
///
/// Returns `Err(size, align)` if creation of a layout with the given size and alignment fails.
pub const fn layout_or_sz_align<T>(n: usize) -> Result<Layout, (usize, usize)> {
    let (sz, align) = (T::SZ, T::ALIGN);

    if sz != 0 && n > (((USIZE_MAX_NO_HIGH_BIT) + 1) - align) / sz {
        return Err((sz, align));
    }

    unsafe { Ok(Layout::from_size_align_unchecked(sz * n, align)) }
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
/// ```rust
/// # use core::ptr::NonNull;
/// # use memapi::{helpers::AllocGuard, Alloc, DefaultAlloc};
/// # let alloc = DefaultAlloc;
/// // Allocate space for one `u32` and wrap it in a guard
/// let layout = core::alloc::Layout::new::<u32>();
/// let mut guard = AllocGuard::new(alloc.alloc(layout).unwrap().cast::<u32>(), &alloc);
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
    alloc: &'a A,
}

impl<'a, T: ?Sized, A: Alloc + ?Sized> AllocGuard<'a, T, A> {
    const_if! {
        "extra_const",
        "Creates a new guard from a pointer and a reference to an allocator.",
        pub const fn new(ptr: NonNull<T>, alloc: &'a A) -> AllocGuard<'a, T, A> {
            AllocGuard { ptr, alloc }
        }
    }

    const_if! {
        "extra_extra_const",
        "Initializes the value by writing to the contained pointer.",
        #[cfg_attr(miri, track_caller)]
        pub const fn init(&mut self, elem: T)
        where
            T: Sized
        {
            unsafe {
                ptr::write(self.ptr.as_ptr(), elem);
            }
        }
    }

    const_if! {
        "extra_const",
        "Releases ownership of the allocation, preventing deallocation, and returns the raw \
        pointer.",
        #[must_use]
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
        unsafe {
            self.alloc.dealloc(self.ptr.cast::<u8>(), self.ptr.layout());
        }
    }
}

impl<T: ?Sized, A: Alloc + ?Sized> Deref for AllocGuard<'_, T, A> {
    type Target = NonNull<T>;

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
/// ```rust
/// # use core::{ptr::NonNull, alloc::Layout};
/// # use memapi::{
/// #  helpers::SliceAllocGuard,
/// #  Alloc,
/// #  DefaultAlloc,
/// #  type_props::SizedProps
/// # };
/// # let alloc = DefaultAlloc;
/// # let len = 5;
///
/// let mut guard = SliceAllocGuard::new(
///     alloc.alloc(unsafe { Layout::from_size_align_unchecked(u32::SZ * len, u32::ALIGN) })
///             .unwrap().cast(),
///     &alloc,
///     len
/// );
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
    full: usize,
}

impl<'a, T, A: Alloc + ?Sized> SliceAllocGuard<'a, T, A> {
    const_if! {
        "extra_const",
        "Creates a new slice guard for `full` elements at `ptr` in the given allocator.",
        pub const fn new(ptr: NonNull<T>, alloc: &'a A, full: usize)
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
        "extra_const",
        "Release ownership of the slice without deallocating memory, returning a `NonNull<T>` \
        pointer to the slice.",
        #[must_use]
        pub const fn release(self) -> NonNull<[T]> {
            let ret = self.get_init_part();
            forget(self);
            ret
        }
    }

    const_if! {
        "extra_const",
        "Release ownership of the slice without deallocating memory, returning a `NonNull<T>` \
        pointer to the slice's first element.",
        #[must_use]
        pub const fn release_first(self) -> NonNull<T> {
            let ret = self.ptr;
            forget(self);
            ret
        }
    }

    const_if! {
        "extra_const",
        "Gets a `NonNull<[T]>` pointer to the initialized elements of the slice.",
        #[cfg_attr(miri, track_caller)]
        #[must_use]
        pub const fn get_init_part(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(self.ptr, self.init)
        }
    }

    const_if! {
        "extra_const",
        "Gets a `NonNull<[T]>` pointer to the uninitialized elements of the slice.",
        #[must_use]
        pub const fn get_uninit_part(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(
                unsafe { NonNull::new_unchecked(self.ptr.as_ptr().add(self.init)) },
                self.full - self.init,
            )
        }
    }

    const_if! {
        "extra_const",
        "Gets a `NonNull<[T]>` pointer to the full slice.",
        #[cfg_attr(miri, track_caller)]
        #[must_use]
        pub const fn get_full(&self) -> NonNull<[T]> {
            nonnull_slice_from_raw_parts(self.ptr, self.full)
        }
    }

    const_if! {
        "extra_extra_const",
        "Sets the initialized element count.\n\n# Safety\n\nThe caller must ensure the new \
        count is correct.",
        pub const unsafe fn set_init(&mut self, init: usize) {
            self.init = init;
        }
    }

    const_if! {
        "extra_extra_const",
        "Initializes the next element of the slice with `elem`.\n\n# Errors\n\nReturns \
        `Err(elem)` if the slice is at capacity.",
        pub const fn init(&mut self, elem: T) -> Result<(), T> {
            if self.init == self.full {
                return Err(elem);
            }
            unsafe {
                self.init_unchecked(elem);
            }
            Ok(())
        }
    }

    const_if! {
        "extra_extra_const",
        "Initializes the next element of the slice with `elem`.\n\n# Safety\n\nThe caller must \
        ensure that the slice is not at capacity. (`initialized() < full()`)",
        pub const unsafe fn init_unchecked(&mut self, elem: T) {
            ptr::write(self.ptr.as_ptr().add(self.init), elem);
            self.init += 1;
        }
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
                Some(elem) => unsafe {
                    ptr::write(self.ptr.as_ptr().add(self.init), elem);
                    self.init += 1;
                },
                None => return Ok(()),
            }
        }
    }

    const_if! {
        "extra_const",
        "Returns how many elements have been initialized.",
        #[must_use]
        pub const fn initialized(&self) -> usize {
            self.init
        }
    }

    const_if! {
        "extra_const",
        "Returns the total number of elements in the slice.",
        #[must_use]
        pub const fn full(&self) -> usize {
            self.full
        }
    }

    const_if! {
        "extra_const",
        "Returns `true` if every element in the slice has been initialized.",
        #[must_use]
        pub const fn is_full(&self) -> bool {
            self.init == self.full
        }
    }

    const_if! {
        "extra_const",
        "Returns `true` if no elements have been initialized.",
        #[must_use]
        pub const fn is_empty(&self) -> bool {
            self.init == 0
        }
    }

    const_if! {
        "extra_extra_const",
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

    // TODO: other *_from_slice methods
}

impl<T, A: Alloc + ?Sized> Drop for SliceAllocGuard<'_, T, A> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(slice_ptr_from_raw_parts(self.ptr.as_ptr(), self.init));
            self.alloc.dealloc(
                self.ptr.cast(),
                Layout::from_size_align_unchecked(T::SZ * self.full, T::ALIGN),
            );
        }
    }
}

impl<T, A: Alloc + ?Sized> Deref for SliceAllocGuard<'_, T, A> {
    type Target = NonNull<T>;

    fn deref(&self) -> &NonNull<T> {
        &self.ptr
    }
}
