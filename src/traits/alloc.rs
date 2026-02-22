use {
    crate::{
        error::Error,
        layout::Layout,
        traits::{
            AllocError,
            alloc_mut::{AllocMut, DeallocMut, GrowMut, ReallocMut, ShrinkMut},
            helpers::{default_dealloc_panic, ralloc}
        }
    },
    ::core::{
        convert::From,
        marker::Sized,
        option::Option::{None, Some},
        ptr::{self, NonNull},
        result::Result::{self, Err}
    }
};

#[allow(unused_imports)] use crate::error::Cause;

/// A memory allocation interface.
pub trait Alloc: AllocError + AllocMut {
    // TODO: maybe make return NonNull<T>
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, <Self as AllocError>::Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, <Self as AllocError>::Error> {
        zalloc!(self, alloc, layout)
    }
}

/// A memory allocation interface which can also deallocate memory.
pub trait Dealloc: Alloc + DeallocMut {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](ptr::dangling).
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
    /// This method may panic if the [`try_dealloc`](Dealloc::try_dealloc) implementation returns
    /// an error, or the implementation chooses to panic for any other reason. It will not panic if
    /// `ptr` is [dangling](ptr::dangling) or if <code>layout.[size](Layout::size)() == 0</code>.
    #[track_caller]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        default_dealloc!(self.try_dealloc, ptr, layout);
    }

    /// Attempts to deallocate a previously allocated block. If this allocator is backed by an
    /// allocation library which does not provide fallible deallocation operations, this may panic,
    /// abort, or incorrectly return `Ok(())`.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](ptr::dangling).
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// <code>Err([Error::Unsupported])</code> if deallocation is unsupported. In this case,
    /// reallocation via [`Grow`], [`Shrink`], and [`Realloc`] may still be supported.
    ///
    /// However, if the `alloc_mut` feature is enabled, and using this method on a synchronization
    /// primitive wrapping a type which implements [`AllocMut`], an
    /// [`Error::Other`] wrapping a generic error message will be returned if locking the primitive
    /// fails.
    ///
    /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    unsafe fn try_dealloc(
        &self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocError>::Error>;

    /// Attempts to deallocate a previously allocated block after performing validity checks.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](ptr::dangling).
    ///
    /// This method must return an error rather than silently accepting the deallocation and
    /// potentially causing UB.
    ///
    /// Note that the default for this method simply returns <code>Err([Error::Unsupported])</code>.
    ///
    /// # Errors
    ///
    /// Implementations commonly return:
    /// - <code>Err([Error::Unsupported])</code> if checked deallocation is unsupported.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If the
    ///   `alloc_mut` feature is enabled, and using this method on a synchronization primitive
    ///   wrapping a type which implements [`AllocMut`], a generic error message will also be
    ///   returned if locking the primitive fails.
    ///
    /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    fn checked_dealloc(
        &self,
        _ptr: NonNull<u8>,
        _layout: Layout
    ) -> Result<(), <Self as AllocError>::Error> {
        Err(<Self as AllocError>::Error::from(Error::Unsupported))
    }
}

/// A memory allocation interface which can also grow allocations.
pub trait Grow: Alloc + Dealloc + GrowMut {
    /// Grow the given block to a new, larger layout.
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
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::GrowSmallerNewLayout]\(old_layout.[size](Layout::size)(),
    ///   new_layout.[size](Layout::size)())\)</code> if <code>old_layout.[size](Layout::size)() >
    ///   new_layout.[size](Layout::size)()</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocError>::Error> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            Alloc::alloc,
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
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::GrowSmallerNewLayout]\(old_layout.[size](Layout::size)(),
    ///   new_layout.[size](Layout::size)())\)</code> if <code>old_layout.[size](Layout::size)() >
    ///   new_layout.[size](Layout::size)()</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocError>::Error> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            Alloc::zalloc,
            Some(Error::GrowSmallerNewLayout),
            None
        )
    }
}

/// A memory allocation interface which can also shrink allocations.
pub trait Shrink: Alloc + Dealloc + ShrinkMut {
    /// Shrink the given block to a new, smaller layout.
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
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ShrinkLargerNewLayout]\(old_layout.[size](Layout::size)(),
    ///   new_layout.[size](Layout::size)())\)</code> if <code>old_layout.[size](Layout::size)() <
    ///   new_layout.[size](Layout::size)()</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocError>::Error> {
        ralloc(
            self,
            ptr,
            old_layout,
            new_layout,
            Alloc::alloc,
            None,
            Some(Error::ShrinkLargerNewLayout)
        )
    }
}

/// A memory allocation interface which can arbitrarily resize allocations.
pub trait Realloc: Grow + Shrink + ReallocMut {
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
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocError>::Error> {
        ralloc(self, ptr, old_layout, new_layout, Alloc::alloc, None, None)
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
    /// Errors are implementation-defined, refer to [`AllocError::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() ==
    ///   0</code>.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocError>::Error> {
        ralloc(self, ptr, old_layout, new_layout, Alloc::zalloc, None, None)
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
        impl<A: AllocError + ?Sized> AllocError for $t {
            type Error = A::Error;
        }

        #[allow(unused_qualifications)]
        impl<A: Alloc + ?Sized> Alloc for $t {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
                (**self).alloc(layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
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

            unsafe fn try_dealloc(
                &self,
                ptr: NonNull<u8>,
                layout: Layout
            ) -> Result<(), <$t as AllocError>::Error> {
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
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
                (**self).grow(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn zgrow(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
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
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
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
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
                (**self).realloc(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn rezalloc(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocError>::Error> {
                (**self).rezalloc(ptr, old_layout, new_layout)
            }
        }
        )+
    };
}

impl_alloc_ref! { &A, &mut A }
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl_alloc_ref! { ::stdalloc::boxed::Box<A>, ::stdalloc::rc::Rc<A>, ::stdalloc::sync::Arc<A> }

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
macro_rules! sysalloc {
    ($self:ident, $alloc:ident, $layout:ident) => {
        crate::helpers::null_q_dyn_zsl_check(
            $layout,
            // SAFETY: System::$alloc is only called after the layout is verified non-zero-sized.
            |layout| unsafe { ::stdalloc::alloc::GlobalAlloc::$alloc($self, layout.to_stdlib()) }
        )
    };
}

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl AllocError for ::std::alloc::System {
    type Error = Error;
}

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Alloc for ::std::alloc::System {
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
impl Dealloc for ::std::alloc::System {
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if !layout.is_zsl() && ptr != layout.dangling() {
            ::stdalloc::alloc::GlobalAlloc::dealloc(self, ptr.as_ptr(), layout.to_stdlib());
        }
    }

    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        self.dealloc(ptr, layout);
        ::core::result::Result::Ok(())
    }
}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Grow for ::std::alloc::System {}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Shrink for ::std::alloc::System {}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Realloc for ::std::alloc::System {}
