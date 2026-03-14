use {
    crate::{
        error::Error,
        layout::Layout,
        traits::{
            AllocDescriptor,
            AllocFeatures,
            alloc::{Alloc, Dealloc, Realloc},
            helpers::{default_dealloc_panic, ralloc_mut}
        }
    },
    ::core::{
        convert::From,
        marker::Sized,
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
    /// If <code>layout.[size](Layout::size)() == 0</code>, no allocation will be performed and a
    /// [dangling](::core::ptr::dangling) pointer will be returned.
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
    ///   be the error from `::std::io::Error::last_os_error().raw_os_error()`.
    fn alloc_mut(
        &mut self,
        layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// If <code>layout.[size](Layout::size)() == 0</code>, no allocation will be performed and a
    /// [dangling](::core::ptr::dangling) pointer will be returned.
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
    ///   be the error from `::std::io::Error::last_os_error().raw_os_error()`.
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
    /// it receives invalid inputs. However, if it is supported, implementations should prefer to
    /// delegate to `CheckedDealloc::checked_dealloc` and thus avoid UB.
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
    /// reallocation via [`Realloc`] may still be supported.
    ///
    /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    unsafe fn try_dealloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocDescriptor>::Error>;
}

/// A memory allocation interface which may require mutable access to itself and can arbitrarily
/// resize allocations.
///
/// All types which are [`Realloc`] are also [`ReallocMut`], making this more generic than
/// [`Realloc`].
pub trait ReallocMut: DeallocMut {
    /// Reallocates a block, growing or shrinking as needed. The new alignment may be larger or the
    /// same, but cannot be smaller.
    ///
    /// On grow, preserves existing contents up to <code>old_layout.[size](Layout::size)()</code>,
    /// and on shrink, truncates to <code>new_layout.[size](Layout::size)()</code>.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// If `ptr` is dangling and `old_layout` is zero-sized, this will behave the same as
    /// [`Alloc::alloc`].
    ///
    /// If `new_layout` is zero-sized, assuming that is a valid call (meaning `old_layout` is as
    /// well, and `ptr` is dangling), a new dangling pointer will be returned. This new pointer may
    /// have a different address if <code>new_layout.[align](Layout::align)() >
    /// old_layout.[align](Layout::align)()</code>.
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
    ///   be the error from `::std::io::Error::last_os_error().raw_os_error()`.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(self, ptr, old_layout, new_layout, AllocMut::alloc_mut)
    }

    /// Reallocates a block, growing or shrinking as needed, with extra bytes being zeroed. The new
    /// alignment may be larger or the same, but cannot be smaller.
    ///
    /// On grow, preserves existing contents up to <code>old_layout.[size](Layout::size)()</code>,
    /// and on shrink, truncates to <code>new_layout.[size](Layout::size)()</code>.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// If `ptr` is dangling and `old_layout` is zero-sized, this will behave the same as
    /// [`Alloc::alloc`].
    ///
    /// If `new_layout` is zero-sized, assuming that is a valid call (meaning `old_layout` is as
    /// well, and `ptr` is dangling), a new dangling pointer will be returned. This new pointer may
    /// have a different address if <code>new_layout.[align](Layout::align)() >
    /// old_layout.[align](Layout::align)()</code>.
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
    ///   be the error from `::std::io::Error::last_os_error().raw_os_error()`.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn rezalloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc_mut(self, ptr, old_layout, new_layout, AllocMut::zalloc_mut)
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
pub trait FullAllocMut: ReallocMut + AllocMut + DeallocMut {}

impl<A: AllocMut + DeallocMut> BasicAllocMut for A {}
impl<A: ReallocMut + AllocMut + DeallocMut> FullAllocMut for A {}

impl<A: Alloc + ?Sized> AllocMut for A {
    #[inline(always)]
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, <A as AllocDescriptor>::Error> {
        (*self).alloc(layout)
    }

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
            fn alloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .alloc_mut(layout)
            }

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
            unsafe fn try_dealloc(
                &self,
                ptr: NonNull<u8>,
                layout: Layout
            ) -> Result<(), <$t as AllocDescriptor>::Error> {
                tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                    .try_dealloc_mut(ptr, layout)
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
