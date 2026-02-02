use {
    crate::{
        Alloc,
        Dealloc,
        Grow,
        Layout,
        Realloc,
        Shrink,
        error::Error,
        traits::helpers::{
            Bytes,
            alloc_mut::{grow_mut, ralloc_mut, shrink_unchecked_mut},
            default_dealloc_panic
        }
    },
    core::{
        cmp::Ordering,
        ptr::{self, NonNull}
    }
};

/// A memory allocation interface which may require mutable access to itself to perform operations.
///
/// All types which are [`Alloc`] are also [`AllocMut`], making this more generic than [`Alloc`].
pub trait AllocMut {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer  if <code>[layout.size()](Layout::size) ==
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
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer  if <code>[layout.size()](Layout::size) ==
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
    fn zalloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error> {
        zalloc!(self, alloc_mut, layout)
    }
}

/// A memory allocation interface which may require mutable access to itself to perform operations
/// and can also deallocate memory.
///
/// All types which are [`Dealloc`] are also [`DeallocMut`], making this more generic than
/// [`Dealloc`].
pub trait DeallocMut: AllocMut {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if <code>[layout.size()](Layout::size) == 0</code>.
    ///
    /// The default implementation simply calls [`try_dealloc_mut`](DeallocMut::try_dealloc_mut) and
    /// panics if it returns an error.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Panics
    ///
    /// This function may panic if the [`try_dealloc_mut`](DeallocMut::try_dealloc_mut)
    /// implementation returns an error, or the implementation chooses to panic for any other
    /// reason.
    #[track_caller]
    #[inline]
    unsafe fn dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if let Err(e) = self.try_dealloc_mut(ptr, layout) {
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
    /// However, if using this method through a synchronization primitive wrapping a type which
    /// implements [`DeallocMut`], an [`Error::Other`] wrapping a generic error message will be
    /// returned if acquiring mutable access to the allocator fails.
    unsafe fn try_dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error>;
}

/// A memory allocation interface which may require mutable access to itself and can also grow
/// allocations.
///
/// All types which are [`Grow`] are also [`GrowMut`], making this more generic than [`Grow`].
pub trait GrowMut: AllocMut + DeallocMut {
    /// Grows the given block to a new, larger layout.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Note that the default implementation simply:
    /// 1. Checks that the new layout is larger or the same size. If both layouts are the same,
    ///    `ptr` is returned and no operation is performed.
    /// 2. Allocates a new block of memory via [`AllocMut::alloc_mut`].
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
    unsafe fn grow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        grow_mut(self, ptr, old_layout, new_layout, Bytes::Uninitialized)
    }

    /// Grows the given block to a new, larger layout, with extra bytes being zeroed.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Note that the default implementation simply:
    /// 1. Checks that the new layout is larger or the same size. If both layouts are the same,
    ///    `ptr` is returned and no operation is performed.
    /// 2. Allocates a new block of memory via [`AllocMut::zalloc_mut`].
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
    unsafe fn zgrow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        grow_mut(self, ptr, old_layout, new_layout, Bytes::Zeroed)
    }
}

/// A memory allocation interface which may require mutable access to itself and can also shrink
/// allocations.
///
/// All types which are [`Shrink`] are also [`ShrinkMut`], making this more generic than [`Shrink`].
pub trait ShrinkMut: AllocMut + DeallocMut {
    /// Shrinks the given block to a new, smaller layout.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer  if <code>[new_layout.size()](Layout::size) ==
    /// 0</code>.
    ///
    /// Note that the default implementation simply:
    /// 1. Checks that the new layout is smaller or the same size. If both layouts are the same,
    ///    `ptr` is returned and no operation is performed.
    /// 2. Allocates a new block of memory via [`AllocMut::alloc_mut`].
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
    unsafe fn shrink_mut(
        &mut self,
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
                    shrink_unchecked_mut(self, ptr, old_layout, new_layout)
                } else {
                    Ok(ptr)
                }
            }
            Ordering::Greater => shrink_unchecked_mut(self, ptr, old_layout, new_layout)
        }
    }
}

/// A memory allocation interface which may require mutable access to itself and can arbitrarily
/// resize allocations.
///
/// All types which are [`Realloc`] are also [`ReallocMut`], making this more generic than
/// [`Realloc`].
pub trait ReallocMut: GrowMut + ShrinkMut {
    /// Reallocates a block, growing or shrinking as needed.
    ///
    /// On grow, preserves existing contents up to [`old_layout.size()`](Layout::size), and on
    /// shrink, truncates to [`new_layout.size()`](Layout::size).
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer  if <code>[new_layout.size()](Layout::size) ==
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
    unsafe fn realloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        ralloc_mut(self, ptr, old_layout, new_layout, Bytes::Uninitialized)
    }

    /// Reallocates a block, growing or shrinking as needed, with extra bytes being zeroed.
    ///
    /// On grow, preserves existing contents up to [`old_layout.size()`](Layout::size), and on
    /// shrink, truncates to [`new_layout.size()`](Layout::size).
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// Returns a [`dangling`](ptr::dangling) pointer  if <code>[new_layout.size()](Layout::size) ==
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
    unsafe fn rezalloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        ralloc_mut(self, ptr, old_layout, new_layout, Bytes::Zeroed)
    }
}

/// A memory allocation interface which may require mutable access and can allocate and deallocate.
///
/// This exists solely because it reads more nicely than <code>A: [DeallocMut]</code>; the two are
/// the same.
pub trait BasicAllocMut: AllocMut + DeallocMut {}
/// A memory allocation interface which may require mutable access and can allocate, deallocate,
/// and arbitrarily resize allocations.
///
/// This exists solely because it reads more nicely than <code>A: [ReallocMut]</code>; the two are
/// the same.
pub trait FullAllocMut: ReallocMut + GrowMut + ShrinkMut + AllocMut + DeallocMut {}

impl<A: AllocMut + DeallocMut> BasicAllocMut for A {}
impl<A: ReallocMut + GrowMut + ShrinkMut + AllocMut + DeallocMut> FullAllocMut for A {}

impl<A: Alloc + ?Sized> AllocMut for A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error> {
        (*self).alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn zalloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error> {
        (*self).zalloc(layout)
    }
}

impl<A: Dealloc + ?Sized> DeallocMut for A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) {
        (*self).dealloc(ptr, layout);
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn try_dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        (*self).try_dealloc(ptr, layout)
    }
}

impl<A: Grow + ?Sized> GrowMut for A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn grow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (*self).grow(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn zgrow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (*self).zgrow(ptr, old_layout, new_layout)
    }
}

impl<A: Shrink + ?Sized> ShrinkMut for A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn shrink_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (*self).shrink(ptr, old_layout, new_layout)
    }
}

impl<A: Realloc + ?Sized> ReallocMut for A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn realloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (*self).realloc(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn rezalloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error> {
        (*self).rezalloc(ptr, old_layout, new_layout)
    }
}

// no AllocMut for &mut A: AllocMut because rust is dumb and "downstream crates may implement Alloc
// for &mut A: AllocMut"

// TODO: decide on inlining for the below
macro_rules! impl_alloc_for_sync_mutalloc {
    ($t:ty, $borrow_call:ident, $($borrow_wrap:ident,)? $err_verb:literal, $t_desc:literal) => {
        impl<A: AllocMut + ?Sized> Alloc for $t {
            #[cfg_attr(miri, track_caller)]
            fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "AllocMut> for immutable allocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                ).alloc_mut(layout)
            }

            #[cfg_attr(miri, track_caller)]
            fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "AllocMut> for immutable allocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                ).zalloc_mut(layout)
            }
        }

        impl<A: DeallocMut + ?Sized> Dealloc for $t {
            #[track_caller]
            unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
                match $($borrow_wrap)?(self.$borrow_call()) {
                    Ok(mut guard) => guard.dealloc_mut(ptr, layout),
                    Err(_) => default_dealloc_panic(
                        ptr,
                        layout,
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "DeallocMut> for `Dealloc` deallocation call"
                        )),
                    ),
                }
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "DeallocMut> for `Dealloc` deallocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                )
                .try_dealloc_mut(ptr, layout)
            }
        }

        impl<A: GrowMut + ?Sized> Grow for $t {
            #[cfg_attr(miri, track_caller)]
            unsafe fn grow(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "GrowMut> for `Grow` reallocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                )
                .grow_mut(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn zgrow(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "GrowMut> for `Grow` reallocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                )
                .zgrow_mut(ptr, old_layout, new_layout)
            }
        }

        impl<A: ShrinkMut + ?Sized> Shrink for $t {
            #[cfg_attr(miri, track_caller)]
            unsafe fn shrink(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "ShrinkMut> for `Shrink` reallocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                )
                .shrink_mut(ptr, old_layout, new_layout)
            }
        }

        impl<A: ReallocMut + ?Sized> Realloc for $t {
            #[cfg_attr(miri, track_caller)]
            unsafe fn realloc(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "ReallocMut> for `Realloc` reallocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                )
                .realloc_mut(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn rezalloc(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, Error> {
                tri!(
                    cmap(
                        Error::Other(concat!(
                            "failed to ",
                            $err_verb,
                            $t_desc,
                            "ReallocMut> for `Realloc` reallocation call"
                        ))
                    )
                    $($borrow_wrap)?(self.$borrow_call())
                )
                .rezalloc_mut(ptr, old_layout, new_layout)
            }
        }
    };
}

#[cfg(feature = "std")]
impl_alloc_for_sync_mutalloc! {
    std::sync::Mutex<A>, lock, "lock ", "Mutex<impl "
}
#[cfg(feature = "std")]
impl_alloc_for_sync_mutalloc! {
    std::sync::RwLock<A>, write, "write lock ", "RwLock<impl "
}
impl_alloc_for_sync_mutalloc! {
    core::cell::RefCell<A>, try_borrow_mut, "mutably borrow ", "RefCell<impl "
}
