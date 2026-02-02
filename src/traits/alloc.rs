use {
    crate::{
        Layout,
        error::Error,
        traits::helpers::{Bytes, default_dealloc_panic, grow, ralloc, shrink_unchecked}
    },
    core::{
        cmp::Ordering,
        ptr::{self, NonNull}
    }
};

/// A memory allocation interface.
pub trait Alloc {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer if <code>[layout.size()](Layout::size) ==
    /// 0</code>.
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
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer if <code>[layout.size()](Layout::size) ==
    /// 0</code>.
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
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        zalloc!(self, alloc, layout)
    }
}

/// A memory allocation interface which can also deallocate memory.
pub trait Dealloc: Alloc {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if <code>[layout.size()](Layout::size) == 0</code>.
    ///
    /// The default implementation simply calls [`try_dealloc`](Dealloc::try_dealloc) and panics if
    /// it returns an error.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Panics
    ///
    /// This function may panic if the [`try_dealloc`](Dealloc::try_dealloc) implementation returns
    /// an error, or the implementation chooses to panic for any other reason.
    #[track_caller]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if let Err(e) = self.try_dealloc(ptr, layout) {
            default_dealloc_panic(ptr, layout, e)
        }
    }

    /// Attempts to deallocate a previously allocated block. If this allocator is backed by an
    /// allocation library which does not provide fallible deallocation operations, this may panic,
    /// abort, or incorrectly return `Ok(())`.
    ///
    /// This is a noop if <code>[layout.size()](Layout::size) == 0</code>.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations do not return any errors, as the library functions backing them
    /// are infallible.
    ///
    /// However, if the `alloc_mut` feature is enabled, and using this method on a synchronization
    /// primitive wrapping a type which implements [`AllocMut`](crate::AllocMut), an
    /// [`Error::Other`] wrapping a generic error message will be returned if locking the primitive
    /// fails.
    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error>;
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
    #[inline]
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
    /// Returns a [`dangling`](ptr::dangling) pointer if <code>[layout.size()](Layout::size) ==
    /// 0</code>.
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
    /// Returns a [`dangling`](ptr::dangling) pointer if <code>[layout.size()](Layout::size) ==
    /// 0</code>.
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
    #[inline]
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
    /// Returns a [`dangling`](ptr::dangling) pointer if <code>[layout.size()](Layout::size) ==
    /// 0</code>.
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
    #[inline]
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

macro_rules! impl_alloc_ref {
    ($($t:ty),+) => {
        $(
        #[allow(unused_qualifications)]
        impl<A: Alloc + ?Sized> Alloc for $t {
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
        #[allow(unused_qualifications)]
        impl<A: Dealloc + ?Sized> Dealloc for $t {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
                (**self).dealloc(ptr, layout);
            }

            unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
                (**self).try_dealloc(ptr, layout)
            }
        }
        #[allow(unused_qualifications)]
        impl<A: Grow + ?Sized> Grow for $t {
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
        #[allow(unused_qualifications)]
        impl<A: Shrink + ?Sized> Shrink for $t {
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
        #[allow(unused_qualifications)]
        impl<A: Realloc + ?Sized> Realloc for $t {
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
        )+
    };
}

impl_alloc_ref! { &A, &mut A }
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl_alloc_ref! { alloc::boxed::Box<A>, alloc::rc::Rc<A>, alloc::sync::Arc<A> }

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
macro_rules! sysalloc {
    ($self:ident, $alloc:ident, $layout:ident) => {
        crate::helpers::null_q_dyn_zsl_check(
            $layout,
            // SAFETY: System::$alloc is only called after the layout is verified non-zero-sized.
            |layout| unsafe { alloc::alloc::GlobalAlloc::$alloc($self, layout.to_stdlib()) }
        )
    };
}

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Alloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        sysalloc!(self, alloc, layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        sysalloc!(self, alloc_zeroed, layout)
    }
}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Dealloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.is_nonzero_sized() {
            alloc::alloc::GlobalAlloc::dealloc(self, ptr.as_ptr(), layout.to_stdlib());
        }
    }

    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        self.dealloc(ptr, layout);
        Ok(())
    }
}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Grow for std::alloc::System {}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Shrink for std::alloc::System {}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Realloc for std::alloc::System {}
