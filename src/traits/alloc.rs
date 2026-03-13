use {
    crate::{
        layout::Layout,
        traits::{
            AllocDescriptor,
            AllocFeatures,
            alloc_mut::{AllocMut, DeallocMut, ReallocMut},
            helpers::{default_dealloc_panic, ralloc}
        }
    },
    ::core::{
        marker::Sized,
        ptr::{self, NonNull},
        result::Result::{self}
    }
};

#[allow(unused_imports)] use crate::error::Cause;

/// A memory allocation interface.
pub trait Alloc: AllocDescriptor + AllocMut {
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
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures. If the
    ///   `alloc_mut` feature is enabled, and using this method on a synchronization primitive
    ///   wrapping a type which implements [`AllocMut`], a generic error message will also be
    ///   returned if locking the primitive fails.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

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
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures. If the
    ///   `alloc_mut` feature is enabled, and using this method on a synchronization primitive
    ///   wrapping a type which implements [`AllocMut`], a generic error message will also be
    ///   returned if locking the primitive fails.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
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
    /// However, if the `alloc_mut` feature is enabled, and using this method on a synchronization
    /// primitive wrapping a type which implements [`DeallocMut`], an
    /// [`Error::Other`] wrapping a generic error message will be returned if locking the primitive
    /// fails.
    ///
    /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    unsafe fn try_dealloc(
        &self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocDescriptor>::Error>;
}

/// A memory allocation interface which can arbitrarily resize allocations.
pub trait Realloc: ReallocMut + Dealloc {
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
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures. If the
    ///   `alloc_mut` feature is enabled, and using this method on a synchronization primitive
    ///   wrapping a type which implements [`ReallocMut`], a generic error message will also be
    ///   returned if locking the primitive fails.
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
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc(self, ptr, old_layout, new_layout, Alloc::alloc)
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
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures. If the
    ///   `alloc_mut` feature is enabled, and using this method on a synchronization primitive
    ///   wrapping a type which implements [`ReallocMut`], a generic error message will also be
    ///   returned if locking the primitive fails.
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
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
        ralloc(self, ptr, old_layout, new_layout, Alloc::zalloc)
    }
}

/// A memory allocation interface which can allocate and deallocate.
///
/// This exists solely because it is somewhat clearer to read than <code>A: [Dealloc]</code>; the
/// two are the same.
pub trait BasicAlloc: Alloc + Dealloc {}
/// A memory allocation interface which can allocate, deallocate, and arbitrarily resize
/// allocations.
///
/// This exists solely because it is somewhat clearer to read than <code>A: [Realloc]</code>; the
/// two are the same.
pub trait FullAlloc: Realloc + Alloc + Dealloc {}

impl<A: Alloc + Dealloc> BasicAlloc for A {}
impl<A: Realloc + Alloc + Dealloc> FullAlloc for A {}

macro_rules! impl_alloc_ref {
    ($($t:ty),+) => {
        $(
        #[allow(unused_qualifications)]
        impl<A: AllocDescriptor + ?Sized> AllocDescriptor for $t {
            type Error = A::Error;

            const FEATURES: AllocFeatures = A::FEATURES;
        }

        #[allow(unused_qualifications)]
        impl<A: Alloc + ?Sized> Alloc for $t {
            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn alloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                (**self).alloc(layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            fn zalloc(
                &self,
                layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
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

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn try_dealloc(
                &self,
                ptr: NonNull<u8>,
                layout: Layout
            ) -> Result<(), <$t as AllocDescriptor>::Error> {
                (**self).try_dealloc(ptr, layout)
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
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                (**self).realloc(ptr, old_layout, new_layout)
            }

            #[cfg_attr(miri, track_caller)]
            #[inline(always)]
            unsafe fn rezalloc(
                &self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout
            ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
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
            // SAFETY: layout requires that it has non-zero size
            |l| unsafe { ::stdalloc::alloc::GlobalAlloc::$alloc($self, l.to_stdlib()) },
            $layout
        )
    };
}

#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl AllocDescriptor for ::std::alloc::System {
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
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if !layout.is_zsl() && ptr != layout.dangling() {
            ::stdalloc::alloc::GlobalAlloc::dealloc(self, ptr.as_ptr(), layout.to_stdlib());
        }
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        self.dealloc(ptr, layout);
        ::core::result::Result::Ok(())
    }
}
#[cfg(all(feature = "std", not(feature = "no_alloc")))]
impl Realloc for ::std::alloc::System {}
