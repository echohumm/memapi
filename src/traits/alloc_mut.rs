use {
    crate::{
        Alloc,
        Dealloc,
        Grow,
        Layout,
        Realloc,
        Shrink,
        error::Error,
        traits::helpers::default_dealloc_panic
    },
    core::ptr::NonNull
};
// TODO: docs, actual impls

/// A memory allocation interface which may require mutable access to itself to allocate.
pub trait AllocMut {
    /// See [`Alloc::alloc`].
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error>;

    /// See [`Alloc::zalloc`]. No default implementation yet.
    fn zalloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error>;
}

/// <placeholder>
pub trait DeallocMut: AllocMut {
    /// See [`Dealloc::dealloc`].
    unsafe fn dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if let Err(e) = self.try_dealloc_mut(ptr, layout) {
            default_dealloc_panic(ptr, layout, e)
        }
    }

    /// See [`Dealloc::try_dealloc`].
    unsafe fn try_dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error>;
}

/// <placeholder>
pub trait GrowMut: AllocMut + DeallocMut {
    /// See [`Grow::grow`]. No default implementation yet.
    unsafe fn grow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error>;

    /// See [`Grow::zgrow`].
    unsafe fn zgrow_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error>;
}

/// <placeholder>
pub trait ShrinkMut: AllocMut + DeallocMut {
    /// See [`Shrink::shrink`]. No default implementation yet.
    unsafe fn shrink_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error>;
}

/// <placeholder>
pub trait ReallocMut: GrowMut + ShrinkMut {
    /// See [`Realloc::realloc`]. No default implementation yet.
    unsafe fn realloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error>;

    /// See [`Realloc::rezalloc`]. No default implementation yet.
    unsafe fn rezalloc_mut(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, Error>;
}

/// <placeholder>
pub trait BasicAllocMut: AllocMut + DeallocMut {}
/// <placeholder>
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

// TODO: better error messages
const MUTEX_ALLOC_FAIL: Error =
    Error::Other("failed to lock Mutex<impl AllocMut> for Alloc allocation call");
const MUTEX_DEALLOC_FAIL: Error =
    Error::Other("failed to lock Mutex<impl DeallocMut> for Dealloc deallocation call");

// TODO: doc all extra errors. switch to using like a doc include like stdlib does so i can extend existing docs easily instead of just copy pasting
#[cfg(feature = "std")]
impl<A: AllocMut + ?Sized> Alloc for std::sync::Mutex<A> {
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        tri!(cmap(MUTEX_ALLOC_FAIL) self.lock()).alloc_mut(layout)
    }

    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, Error> {
        tri!(cmap(MUTEX_ALLOC_FAIL) self.lock()).zalloc_mut(layout)
    }
}

#[cfg(feature = "std")]
impl<A: DeallocMut + ?Sized> Dealloc for std::sync::Mutex<A> {
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        match self.lock() {
            Ok(mut lock) => lock.dealloc_mut(ptr, layout),
            Err(_) => default_dealloc_panic(ptr, layout, MUTEX_DEALLOC_FAIL),
        }
    }

    unsafe fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        tri!(cmap(MUTEX_DEALLOC_FAIL) self.lock()).try_dealloc_mut(ptr, layout)
    }
}
