use {
    crate::{
        error::Error,
        layout::Layout,
        traits::{
            AllocDescriptor,
            AllocFeatures,
            alloc::{Alloc, Dealloc, Grow, Realloc, Shrink},
            helpers::{default_dealloc_panic, ralloc_mut}
        }
    },
    ::core::{
        convert::From,
        marker::Sized,
        option::Option::{None, Some},
        ptr::{self, NonNull},
        result::Result::{self}
    }
};

/// A memory allocation interface which may require mutable access to itself to perform operations.
///
/// All types which are [`Alloc`] are also [`AllocMut`], making this more generic than [`Alloc`].
pub trait AllocMut: AllocDescriptor {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    fn alloc_mut(
        &mut self,
        layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc_mut(
        &mut self,
        layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        zalloc!(self, alloc_mut, layout)
    }
}

/// A memory allocation interface which may require mutable access to itself and can also deallocate
/// memory.
///
/// All types which are [`Dealloc`] are also [`DeallocMut`], making this more generic than
/// [`Dealloc`].
pub trait DeallocMut: AllocMut {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](ptr::dangling).
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
    /// This method may panic if the [`try_dealloc_mut`](DeallocMut::try_dealloc_mut)
    /// implementation returns an error, or the implementation chooses to panic for any other
    /// reason. It will not panic if `ptr` is [dangling](ptr::dangling) or
    /// if <code>layout.[size](Layout::size)() == 0</code>.
    #[track_caller]
    #[inline]
    unsafe fn dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) {
        default_dealloc!(self.try_dealloc_mut, ptr, layout);
    }

    /// Attempts to deallocate a previously allocated block. If this allocator is backed by an
    /// allocation library which does not provide fallible deallocation operations, this may panic,
    /// abort, or incorrectly return `Ok(())`.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](ptr::dangling).
    ///
    /// Note that this function differs from checked deallocation in that it may still cause UB if
    /// it receives invalid inputs.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// <code>Err([Error::Unsupported])</code> if deallocation is unsupported. In this case,
    /// reallocation via [`Grow`], [`Shrink`], and [`Realloc`] may still be supported.
    ///
    /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    unsafe fn try_dealloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocDescriptor>::Error>;
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
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::GrowSmallerNewLayout]\(old_layout.[size](Layout::size)(),
    ///   new_layout.[size](Layout::size)())\)</code> if <code>old_layout.[size](Layout::size)() >
    ///   new_layout.[size](Layout::size)()</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>new_layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocMut::alloc_mut,
            Some(Error::GrowSmallerNewLayout),
            None
        )
    }

    /// Grows the given block to a new, larger layout, with extra bytes being zeroed.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::GrowSmallerNewLayout]\(old_layout.[size](Layout::size)(),
    ///   new_layout.[size](Layout::size)())\)</code> if <code>old_layout.[size](Layout::size)() >
    ///   new_layout.[size](Layout::size)()</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>new_layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zgrow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocMut::zalloc_mut,
            Some(Error::GrowSmallerNewLayout),
            None
        )
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
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `old_layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ShrinkLargerNewLayout]\(old_layout.[size](Layout::size)(),
    ///   new_layout.[size](Layout::size)())\)</code> if <code>old_layout.[size](Layout::size)() <
    ///   new_layout.[size](Layout::size)()</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>new_layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocMut::alloc_mut,
            None,
            Some(Error::ShrinkLargerNewLayout)
        )
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
    /// On grow, preserves existing contents up to <code>old_layout.[size](Layout::size)()</code>,
    /// and on shrink, truncates to <code>new_layout.[size](Layout::size)()</code>.
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
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>new_layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(self, ptr, old_layout, new_layout, AllocMut::alloc_mut, None, None)
    }

    /// Reallocates a block, growing or shrinking as needed, with extra bytes being zeroed.
    ///
    /// On grow, preserves existing contents up to <code>old_layout.[size](Layout::size)()</code>,
    /// and on shrink, truncates to <code>new_layout.[size](Layout::size)()</code>.
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
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`](crate::error::Cause::Unknown). If the `os_err_reporting`
    ///   feature is enabled, it will be
    ///   <code>[Cause::OSErr](crate::error::Cause::OSErr)(oserr)</code>. In this case, `oserr` will
    ///   be the error from <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>new_layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn rezalloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(self, ptr, old_layout, new_layout, AllocMut::alloc_mut, None, None)
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
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
        (*self).alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn zalloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
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
    unsafe fn try_dealloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <A as AllocDescriptor>::Error> {
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
    ) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
        (*self).grow(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn zgrow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
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
    ) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
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
    ) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
        (*self).realloc(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn rezalloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
        (*self).rezalloc(ptr, old_layout, new_layout)
    }
}

// no AllocMut for &mut A: AllocMut because rust is dumb and "downstream crates may implement Alloc
// for &mut A"

const LOCK_ERR: Error = Error::Other("lock failed");

macro_rules! impl_alloc_for_sync_mutalloc {
    ($t:ty, $borrow_call:ident) => {
        impl<A: AllocDescriptor + ?Sized> AllocDescriptor for $t {
            type Error = A::Error;

            const FEATURES: AllocFeatures = A::FEATURES;
        }

        impl<A: AllocMut + ?Sized> Alloc for $t {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn alloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .alloc_mut(layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .zalloc_mut(layout)
            }
        }

        impl<A: DeallocMut + ?Sized> Dealloc for $t {
            #[cfg_attr(miri, track_caller)]
            #[inline]
            unsafe fn try_dealloc(
                &self,
                ptr: NonNull<u8>,
                layout: Layout
            ) -> Result<(), <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
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
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .grow_mut(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn zgrow(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
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
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
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
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .realloc_mut(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            unsafe fn rezalloc(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .rezalloc_mut(ptr, old_layout, new_layout)
            }
        }
    };
}

#[cfg(feature = "std")]
impl_alloc_for_sync_mutalloc! {
    ::std::sync::Mutex<A>, lock
}
#[cfg(feature = "std")]
impl_alloc_for_sync_mutalloc! {
    ::std::sync::RwLock<A>, write
}
impl_alloc_for_sync_mutalloc! {
    ::core::cell::RefCell<A>, try_borrow_mut
}
