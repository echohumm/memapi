use {
    crate::{Layout, error::Error, helpers::alloc_then},
    core::{
        cmp::Ordering,
        ptr::{self, NonNull}
    }
};

/// A memory allocation interface.
pub trait Alloc {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    /// - <code>[Error::ZeroSizedLayout]\([layout.dangling()](Layout::dangling)\)</code> if
    ///   <code>[layout.size()](Layout::size) == 0</code>.
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    /// - <code>[Error::ZeroSizedLayout]\([layout.dangling()](Layout::dangling)\)</code> if
    ///   <code>[layout.size()](Layout::size) == 0</code>.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        // SAFETY: alloc returns at least layout.size() allocated bytes
        unsafe {
            alloc_then(self, layout, (), |p, ()| {
                ptr::write_bytes(p.as_ptr(), 0, layout.size());
                p
            })
        }
    }
}

/// A memory allocation interface which can also deallocate memory.
pub trait Dealloc: Alloc {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if <code>[layout.size()](Layout::size) == 0</code>.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Panics
    ///
    /// Some implementations may choose to panic if `ptr` or `layout` are invalid.
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);
}

/// A memory allocation interface which can also grow allocations.
pub trait Grow: Alloc + Dealloc {
    /// Grow the given block to a new, larger layout.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Note that the default implementation simply:
    /// 1. Checks that the new layout is larger or the same size. If both layouts are the same,
    ///    `ptr` is returned and no operation is performed.
    /// 2. Allocates a new block of memory via [`Alloc::alloc`].
    /// 3. Copies [`old_layout.size()`](Layout::size) bytes from the old block to the new block.
    /// 4. Deallocates the old block.
    /// 5. Returns a pointer to the new block.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    /// - <code>Err([Error::GrowSmallerNewLayout]\([old_layout.size()](Layout::size),
    ///   [new_layout.size()](Layout::size))\)</code> if <code>[old_layout.size()](Layout::size) >
    ///   [new_layout.size()](Layout::size)</code>.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        grow(self, ptr, old_layout, new_layout, Bytes::Uninitialized)
    }

    /// Grows the given block to a new, larger layout, with extra bytes being zeroed.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Note that the default implementation simply:
    /// 1. Checks that the new layout is larger or the same size. If both layouts are the same,
    ///    `ptr` is returned and no operation is performed.
    /// 2. Allocates a new block of memory via [`Alloc::zalloc`].
    /// 3. Copies [`old_layout.size()`](Layout::size) bytes from the old block to the new block.
    /// 4. Deallocates the old block.
    /// 5. Returns a pointer to the new block.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    /// - <code>Err([Error::GrowSmallerNewLayout]\([old_layout.size()](Layout::size),
    ///   [new_layout.size()](Layout::size))\)</code> if <code>[old_layout.size()](Layout::size) >
    ///   [new_layout.size()](Layout::size)</code>.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        grow(self, ptr, old_layout, new_layout, Bytes::Zeroed)
    }
}

/// A memory allocation interface which can also shrink allocations.
pub trait Shrink: Alloc + Dealloc {
    /// Shrink the given block to a new, smaller layout.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Note that the default implementation simply:
    /// 1. Checks that the new layout is smaller or the same size. If both layouts are the same,
    ///    `ptr` is returned and no operation is performed.
    /// 2. Allocates a new block of memory via [`Alloc::alloc`].
    /// 3. Copies [`new_layout.size()`](Layout::size) bytes from the old block to the new block.
    ///    This will discard any extra bytes from the old block.
    /// 4. Deallocates the old block.
    /// 5. Returns a pointer to the new block.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    /// - <code>Err([Error::ShrinkLargerNewLayout]\([old_layout.size()](Layout::size),
    ///   [new_layout.size()](Layout::size))\)</code> if <code>[old_layout.size()](Layout::size) <
    ///   [new_layout.size()](Layout::size)</code>.
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        match old_layout.size().cmp(&new_layout.size()) {
            Ordering::Less => {
                Err(Error::ShrinkLargerNewLayout(old_layout.size(), new_layout.size()))
            }
            Ordering::Equal => {
                if new_layout.align() > old_layout.align() {
                    shrink_unchecked(self, ptr, old_layout, new_layout)
                } else {
                    Ok(ptr)
                }
            }
            Ordering::Greater => shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }
}

/// A memory allocation interface which can arbitrarily resize allocations.
pub trait Realloc: Grow + Shrink {
    /// Reallocates a block, growing or shrinking as needed.
    ///
    /// On grow, preserves existing contents up to [`old_layout.size()`](Layout::size), and on
    /// shrink, truncates to [`new_layout.size()`](Layout::size).
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block previously allocated with this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    // TODO: zsl becomes possible again with shrink/realloc, need to doc that error
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        ralloc(self, ptr, old_layout, new_layout, Bytes::Uninitialized)
    }

    /// Reallocates a block, growing or shrinking as needed, with extra bytes being zeroed.
    ///
    /// On grow, preserves existing contents up to [`old_layout.size()`](Layout::size), and on
    /// shrink, truncates to [`new_layout.size()`](Layout::size).
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block previously allocated with this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        ralloc(self, ptr, old_layout, new_layout, Bytes::Zeroed)
    }
}

/// A memory allocation interface which can allocate and deallocate.
///
/// This exists solely because it reads more nicely than <code>A: [Dealloc]</code>; the two are the
/// same.
pub trait BasicAlloc: Alloc + Dealloc {}
/// A memory allocation interface which can allocate, deallocate, and arbitrarily resize
/// allocations.
///
/// This exists solely because it reads more nicely than <code>A: [Realloc]</code>; the two are the
/// same.
pub trait FullAlloc: Realloc + Grow + Shrink + Alloc + Dealloc {}

impl<A: Alloc + Dealloc> BasicAlloc for A {}
impl<A: Realloc + Grow + Shrink + Alloc + Dealloc> FullAlloc for A {}

#[allow(clippy::inline_always)]
impl<A: Alloc + ?Sized> Alloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        (**self).alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        (**self).zalloc(layout)
    }
}
#[allow(clippy::inline_always)]
impl<A: Dealloc + ?Sized> Dealloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        (**self).dealloc(ptr, layout);
    }
}
#[allow(clippy::inline_always)]
impl<A: Grow + ?Sized> Grow for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (**self).grow(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (**self).zgrow(ptr, old_layout, new_layout)
    }
}
#[allow(clippy::inline_always)]
impl<A: Shrink + ?Sized> Shrink for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (**self).shrink(ptr, old_layout, new_layout)
    }
}
#[allow(clippy::inline_always)]
impl<A: Realloc + ?Sized> Realloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (**self).realloc(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (**self).rezalloc(ptr, old_layout, new_layout)
    }
}

#[cfg(feature = "std")]
impl Alloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        crate::helpers::null_q_dyn_zsl_check(
            layout,
            // SAFETY: System::alloc is only called after the layout is verified non-zero-sized.
            |layout| unsafe { alloc::alloc::GlobalAlloc::alloc(self, layout.to_stdlib()) }
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        crate::helpers::null_q_dyn_zsl_check(
            layout,
            // SAFETY: System::alloc_zeroed is only called after the layout is verified
            //  non-zero-sized.
            |layout| unsafe { alloc::alloc::GlobalAlloc::alloc_zeroed(self, layout.to_stdlib()) }
        )
    }
}
#[cfg(feature = "std")]
impl Dealloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            alloc::alloc::GlobalAlloc::dealloc(self, ptr.as_ptr(), layout.to_stdlib());
        }
    }
}
#[cfg(feature = "std")]
impl Grow for std::alloc::System {}
#[cfg(feature = "std")]
impl Shrink for std::alloc::System {}
#[cfg(feature = "std")]
impl Realloc for std::alloc::System {}

// TODO: might just remove these, already removed shrink()
#[cfg_attr(miri, track_caller)]
unsafe fn grow<A: Grow + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, Error> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => grow_unchecked(a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            if new_layout.align() > old_layout.align() {
                grow_unchecked(&a, ptr, old_layout, new_layout, b)
            } else {
                Ok(ptr)
            }
        }
        Ordering::Greater => Err(Error::GrowSmallerNewLayout(old_layout.size(), new_layout.size()))
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function doesn't check for layout validity.
/// The caller must ensure [`new_layout.size()`](Layout::size) is greater than
/// [`old_layout.size()`](Layout::size).
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(miri, track_caller)]
unsafe fn grow_unchecked<A: Grow + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, Error> {
    let old_size = old_layout.size();
    let new_ptr = match b {
        Bytes::Uninitialized => tri!(do a.alloc(new_layout)),
        Bytes::Zeroed => tri!(do a.zalloc(new_layout))
    };

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
    if old_size != 0 {
        a.dealloc(ptr, old_layout);
    }

    Ok(new_ptr)
}

/// Internal helper to shrink the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function doesn't check for layout validity.
/// The caller must ensure [`new_layout.size()`](Layout::size) is greater than
/// [`old_layout.size()`](Layout::size).
#[cfg_attr(miri, track_caller)]
unsafe fn shrink_unchecked<A: Shrink + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout
) -> Result<NonNull<u8>, Error> {
    let new_ptr = tri!(do a.alloc(new_layout));

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
    if old_layout.size() != 0 {
        a.dealloc(ptr, old_layout);
    }

    Ok(new_ptr)
}

#[cfg_attr(miri, track_caller)]
unsafe fn ralloc<A: Realloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, Error> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => grow_unchecked(&a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            if new_layout.align() > old_layout.align() {
                grow_unchecked(&a, ptr, old_layout, new_layout, b)
            } else {
                Ok(ptr)
            }
        }
        Ordering::Greater => shrink_unchecked(&a, ptr, old_layout, new_layout)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Bytes {
    /// Uninitialized bytes.
    Uninitialized,
    /// Zeroed bytes.
    Zeroed
}
