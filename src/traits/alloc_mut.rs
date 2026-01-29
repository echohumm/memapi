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

/// A memory allocation interface which may require mutable access to itself to perform operations.
pub trait AllocMut {
    /// See [`Alloc::alloc`].
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error>;

    /// See [`Alloc::zalloc`]. No default implementation yet.
    fn zalloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error>;
}

/// A memory allocation interface which may require mutable access to itself to perform operations
/// and can also deallocate memory.
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

    /// See [`Grow::zgrow`]. No default implementation.
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

// no AllocMut for &mut A: AllocMut because rust is dumb and "downstream crates may implement Alloc
// for &mut A: AllocMut"

macro_rules! impl_alloc_for_sync_mutalloc {
    ($t:ty, $borrow_call:ident, $($borrow_wrap:ident,)? $err_verb:literal, $t_desc:literal) => {
        impl<A: AllocMut + ?Sized> Alloc for $t {
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
