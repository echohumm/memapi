use {
    crate::{layout::Layout, traits::AllocDescriptor},
    ::core::{ptr::NonNull, result::Result}
};

macro_rules! impl_checked_realloc_group {
    (
        $impl_trait:ident : $bound:ident
            { $($([$self_ex:tt])? $method:ident => $call:ident),+ $(,)? }
    ) => {
        impl<A: $bound + AllocOwned + ?Sized> $impl_trait for A {
            $(
            fn $method(
                & $($self_ex)? self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout
            ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error> {
                tri!(do self.owns(ptr, old_layout));

                // SAFETY: `owns` returned Ok(()), so the implementor guarantees calling this is
                //  fine.
                unsafe { self.$call(ptr, old_layout, new_layout) }
            }
            )+
        }
    };
}

/// A simple trait which, when implemented, automatically implements the checked allocation
/// traits.
///
/// # Safety
///
/// Implementors of this trait must ensure that [`AllocOwned::owns`] returns an error if the pointer
/// or layout it receives would cause UB if passed to a trait method from
/// [`alloc`](crate::traits::alloc).
pub unsafe trait AllocOwned: AllocDescriptor {
    /// A helper to check whether `self` owns the allocation at `ptr`. The layout may be ignored or
    /// validated, so long as the below condition remains true.
    ///
    /// This function *must* return an error if calling any trait method from
    /// [`alloc`](crate::traits::alloc) on the received pointer and layout would result in UB.
    ///
    /// # Errors
    ///
    /// The errors returned by this method are implementation defined.
    fn owns(
        &self,
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocDescriptor>::Error>;
}

/// Variants corresponding to immutable traits, from [`crate::traits::alloc`].
pub mod alloc {
    use {
        crate::{
            layout::Layout,
            prelude::AllocDescriptor,
            traits::{
                alloc::{Alloc, Dealloc, Realloc},
                alloc_checked::AllocOwned
            }
        },
        ::core::{
            marker::Sized,
            ptr::NonNull,
            result::Result::{self, Ok}
        }
    };

    #[allow(unused_imports)] use crate::error::Error;

    /// A memory allocation interface which can also perform deallocation safely.
    pub trait CheckedDealloc: Alloc + Dealloc {
        /// Attempts to deallocate a previously allocated block after performing validity checks.
        ///
        /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
        /// [dangling](::core::ptr::dangling).
        ///
        /// This method must return an error rather than silently accepting the deallocation and
        /// potentially causing UB.
        ///
        /// # Errors
        ///
        /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
        ///
        /// The standard implementations may return:
        /// - <code>Err([Error::Unsupported])</code> if checked deallocation is unsupported. In this
        ///   case, reallocation via [`CheckedRealloc`] may still be supported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If
        ///   the `alloc_mut` feature is enabled, and using this method on a synchronization
        ///   primitive wrapping a type which implements
        ///   [`CheckedDeallocMut`](crate::traits::alloc_checked::alloc_mut::CheckedDeallocMut), a
        ///   generic error message will also be returned if locking the primitive fails.
        ///
        /// This method will not return an error if `ptr` is [dangling](::core::ptr::dangling) or if
        /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
        fn checked_dealloc(
            &self,
            ptr: NonNull<u8>,
            layout: Layout
        ) -> Result<(), <Self as AllocDescriptor>::Error>;
    }

    /// A memory allocation interface which can arbitrarily resize allocations safely.
    ///
    /// This trait is the checked variant of [`Realloc`]. Unlike [`Realloc::realloc`] and
    /// [`Realloc::rezalloc`], its methods are safe to call: they perform validity checks (via
    /// [`AllocOwned`]) and must return an error rather than risking UB when given an invalid
    /// pointer/layout pair.
    pub trait CheckedRealloc: Realloc {
        /// Attempts to reallocate a previously allocated block after performing validity checks.
        ///
        /// On grow, preserves existing contents up to
        /// <code>old_layout.[size](Layout::size)()</code>, and on shrink, truncates to
        /// <code>new_layout.[size](Layout::size)()</code>.
        ///
        /// On failure, the original memory will not be deallocated.
        ///
        /// This method must return an error rather than silently accepting invalid inputs and
        /// potentially causing UB.
        ///
        /// # Errors
        ///
        /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
        ///
        /// The standard implementations may return:
        /// - <code>Err([Error::Unsupported])</code> if checked reallocation is unsupported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If
        ///   the `alloc_mut` feature is enabled, and using this method on a synchronization
        ///   primitive wrapping a type which implements
        ///   [`ReallocMut`](crate::traits::alloc_mut::ReallocMut), a generic error message will
        ///   also be returned if locking the primitive fails.
        fn checked_realloc(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout
        ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

        /// Attempts to reallocate a previously allocated block after performing validity checks,
        /// with extra bytes being zeroed.
        ///
        /// On grow, preserves existing contents up to
        /// <code>old_layout.[size](Layout::size)()</code>, and on shrink, truncates to
        /// <code>new_layout.[size](Layout::size)()</code>.
        ///
        /// On failure, the original memory will not be deallocated.
        ///
        /// This method must return an error rather than silently accepting invalid inputs and
        /// potentially causing UB.
        ///
        /// # Errors
        ///
        /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
        ///
        /// The standard implementations may return:
        /// - <code>Err([Error::Unsupported])</code> if checked reallocation is unsupported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If
        ///   the `alloc_mut` feature is enabled, and using this method on a synchronization
        ///   primitive wrapping a type which implements
        ///   [`ReallocMut`](crate::traits::alloc_mut::ReallocMut), a generic error message will
        ///   also be returned if locking the primitive fails.
        fn checked_rezalloc(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout
        ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;
    }

    impl<A: Dealloc + AllocOwned + ?Sized> CheckedDealloc for A {
        fn checked_dealloc(
            &self,
            ptr: NonNull<u8>,
            layout: Layout
        ) -> Result<(), <Self as AllocDescriptor>::Error> {
            tri!(do self.owns(ptr, layout));

            // SAFETY: `owns` returned Ok(()), so the implementor guarantees calling dealloc is
            // fine.
            unsafe {
                self.dealloc(ptr, layout);
            }
            Ok(())
        }
    }
    impl_checked_realloc_group!(CheckedRealloc : Realloc
        { checked_realloc => realloc, checked_rezalloc => rezalloc });
}

/// Variants corresponding to mutable traits, from [`crate::traits::alloc_mut`].
pub mod alloc_mut {
    use {
        crate::{
            error::Error,
            layout::Layout,
            prelude::AllocDescriptor,
            traits::{
                alloc_checked::{
                    AllocOwned,
                    alloc::{CheckedDealloc, CheckedRealloc}
                },
                alloc_mut::{DeallocMut, ReallocMut}
            }
        },
        ::core::{
            convert::From,
            marker::Sized,
            ptr::NonNull,
            result::Result::{self, Ok}
        }
    };

    /// A memory allocation interface which can also perform checked deallocation, requiring
    /// mutable access.
    pub trait CheckedDeallocMut: DeallocMut {
        /// Attempts to deallocate a previously allocated block after performing validity checks.
        ///
        /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
        /// [dangling](::core::ptr::dangling).
        ///
        /// This method must return an error rather than silently accepting the deallocation and
        /// potentially causing UB.
        ///
        /// Note that the default for this method simply returns
        /// <code>Err([Error::Unsupported])</code>.
        ///
        /// # Errors
        ///
        /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
        ///
        /// The standard implementations may return:
        /// - <code>Err([Error::Unsupported])</code> if checked deallocation is unsupported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures.
        ///
        /// This method will not return an error if `ptr` is [dangling](::core::ptr::dangling) or if
        /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
        fn checked_dealloc_mut(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout
        ) -> Result<(), <Self as AllocDescriptor>::Error>;
    }

    /// A memory allocation interface which can arbitrarily resize allocations safely, requiring
    /// mutable access.
    pub trait CheckedReallocMut: ReallocMut {
        /// Attempts to reallocate a previously allocated block after performing validity checks.
        ///
        /// On grow, preserves existing contents up to
        /// <code>old_layout.[size](Layout::size)()</code>, and on shrink, truncates to
        /// <code>new_layout.[size](Layout::size)()</code>.
        ///
        /// On failure, the original memory will not be deallocated.
        ///
        /// This method must return an error rather than silently accepting invalid inputs and
        /// potentially causing UB.
        ///
        /// # Errors
        ///
        /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
        ///
        /// The standard implementations may return:
        /// - <code>Err([Error::Unsupported])</code> if checked reallocation is unsupported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If
        ///   the `alloc_mut` feature is enabled, and using this method on a synchronization
        ///   primitive wrapping a type which implements [`ReallocMut`], a generic error message
        ///   will also be returned if locking the primitive fails.
        fn checked_realloc_mut(
            &mut self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout
        ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

        /// Attempts to reallocate a previously allocated block after performing validity checks,
        /// with extra bytes being zeroed.
        ///
        /// On grow, preserves existing contents up to
        /// <code>old_layout.[size](Layout::size)()</code>, and on shrink, truncates to
        /// <code>new_layout.[size](Layout::size)()</code>.
        ///
        /// On failure, the original memory will not be deallocated.
        ///
        /// This method must return an error rather than silently accepting invalid inputs and
        /// potentially causing UB.
        ///
        /// # Errors
        ///
        /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
        ///
        /// The standard implementations may return:
        /// - <code>Err([Error::Unsupported])</code> if checked reallocation is unsupported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If
        ///   the `alloc_mut` feature is enabled, and using this method on a synchronization
        ///   primitive wrapping a type which implements [`ReallocMut`], a generic error message
        ///   will also be returned if locking the primitive fails.
        fn checked_rezalloc_mut(
            &mut self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout
        ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;
    }

    impl<A: DeallocMut + AllocOwned + ?Sized> CheckedDeallocMut for A {
        fn checked_dealloc_mut(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout
        ) -> Result<(), <Self as AllocDescriptor>::Error> {
            tri!(do self.owns(ptr, layout));

            // SAFETY: `owns` returned Ok(()), so the implementor guarantees calling dealloc is
            // fine.
            unsafe {
                self.dealloc_mut(ptr, layout);
            }
            Ok(())
        }
    }
    impl_checked_realloc_group!(CheckedReallocMut : ReallocMut
        { [mut] checked_realloc_mut => realloc_mut, [mut] checked_rezalloc_mut => rezalloc_mut });

    const LOCK_ERR: Error = Error::Other("lock failed");

    macro_rules! impl_alloc_for_sync_mutalloc {
        ($t:ty, $borrow_call:ident) => {
            impl<A: CheckedDeallocMut + ?Sized> CheckedDealloc for $t {
                fn checked_dealloc(
                    &self,
                    ptr: NonNull<u8>,
                    layout: Layout
                ) -> Result<(), <$t as AllocDescriptor>::Error> {
                    tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                        .checked_dealloc_mut(ptr, layout)
                }
            }

            impl<A: CheckedReallocMut + ?Sized> CheckedRealloc for $t {
                fn checked_realloc(
                    &self,
                    ptr: NonNull<u8>,
                    old_layout: Layout,
                    new_layout: Layout,
                ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                    tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                        .checked_realloc_mut(ptr, old_layout, new_layout)
                }

               fn checked_rezalloc(
                    &self,
                    ptr: NonNull<u8>,
                    old_layout: Layout,
                    new_layout: Layout,
                ) -> Result<NonNull<u8>, <$t as AllocDescriptor>::Error> {
                    tri!(cmap(LOCK_ERR) from <Self as AllocDescriptor>::Error, self.$borrow_call())
                        .checked_rezalloc_mut(ptr, old_layout, new_layout)
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
}
