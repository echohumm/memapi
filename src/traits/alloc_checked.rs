use {
    crate::{layout::Layout, traits::AllocDescriptor},
    ::core::{ptr::NonNull, result::Result}
};

macro_rules! trait_decl {
    (
        $([$doc:literal, $name:ident : $req:ident,
            ($($fn_doc:literal, $fn_name:ident $(, $self_ex:tt)?):+)]),+
    ) => {
        $(
        #[doc = $doc]
        pub trait $name: $req {
            $(
            #[doc = $fn_doc]
            fn $fn_name(
                & $($self_ex)? self,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout
            ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;
            )+
        }
        )+
    };
}

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
                alloc::{Dealloc, Grow, Realloc, Shrink},
                alloc_checked::AllocOwned
            }
        },
        ::core::{
            marker::Sized,
            ptr::NonNull,
            result::Result::{self, Ok}
        }
    };

    /// <placeholder>
    pub trait CheckedDealloc: Dealloc {
        /// Attempts to deallocate a previously allocated block after performing validity checks.
        ///
        /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
        /// [dangling](ptr::dangling).
        ///
        /// This method must return an error rather than silently accepting the deallocation and
        /// potentially causing UB.
        ///
        /// # Errors
        ///
        /// Implementations commonly return:
        /// - <code>Err([Error::Unsupported])</code> if checked deallocation is unsupported.
        // TODO: in this case ... like normal dealloc
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures. If
        ///   the `alloc_mut` feature is enabled, and using this method on a synchronization
        ///   primitive wrapping a type which implements [`AllocMut`], a generic error message will
        ///   also be returned if locking the primitive fails.
        ///
        /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
        /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
        fn checked_dealloc(
            &self,
            ptr: NonNull<u8>,
            layout: Layout
        ) -> Result<(), <Self as AllocDescriptor>::Error>;
    }

    trait_decl! {
        ["<placeholder>", CheckedShrink: Shrink, ("<placeholder>", checked_shrink)],
        ["<placeholder>", CheckedGrow: Grow,
            ("<placeholder>", checked_grow:"<placeholder>", checked_zgrow)],
        ["<placeholder>", CheckedRealloc: Realloc,
            ("<placeholder>", checked_realloc:"<placeholder>", checked_rezalloc)]
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

    impl_checked_realloc_group!(CheckedShrink : Shrink { checked_shrink => shrink });
    impl_checked_realloc_group!(CheckedGrow : Grow 
        { checked_grow => grow, checked_zgrow => zgrow });
    impl_checked_realloc_group!(CheckedRealloc : Realloc 
        { checked_realloc => realloc, checked_rezalloc => rezalloc });
}

/// Variants corresponding to mutable traits, from [`crate::traits::alloc_mut`].
pub mod alloc_mut {
    use {
        crate::{
            layout::Layout,
            prelude::AllocDescriptor,
            traits::{
                alloc_checked::AllocOwned,
                alloc_mut::{DeallocMut, GrowMut, ReallocMut, ShrinkMut}
            }
        },
        ::core::{
            marker::Sized,
            ptr::NonNull,
            result::Result::{self, Ok}
        }
    };

    /// <placeholder>
    pub trait CheckedDeallocMut: DeallocMut {
        /// Attempts to deallocate a previously allocated block after performing validity checks.
        ///
        /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
        /// [dangling](ptr::dangling).
        ///
        /// This method must return an error rather than silently accepting the deallocation and
        /// potentially causing UB.
        ///
        /// Note that the default for this method simply returns
        /// <code>Err([Error::Unsupported])</code>.
        ///
        /// # Errors
        ///
        /// Implementations commonly return:
        /// - <code>Err([Error::Unsupported])</code> if checked deallocation is unsupported.
        /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific validation failures.
        ///
        /// This method will not return an error if `ptr` is [dangling](ptr::dangling) or if
        /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
        fn checked_dealloc_mut(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout
        ) -> Result<(), <Self as AllocDescriptor>::Error>;
    }

    trait_decl! {
        ["<placeholder>", CheckedShrinkMut: ShrinkMut, ("<placeholder>", checked_shrink_mut, mut)],
        ["<placeholder>", CheckedGrowMut: GrowMut,
            ("<placeholder>", checked_grow_mut, mut:"<placeholder>", checked_zgrow_mut, mut)],
        ["<placeholder>", CheckedReallocMut: ReallocMut,
            ("<placeholder>", checked_realloc_mut, mut:"<placeholder>", checked_rezalloc_mut, mut)]
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

    impl_checked_realloc_group!(CheckedShrinkMut : ShrinkMut
        { [mut] checked_shrink_mut => shrink_mut });
    impl_checked_realloc_group!(CheckedGrowMut : GrowMut
        { [mut] checked_grow_mut => grow_mut, [mut] checked_zgrow_mut => zgrow_mut });
    impl_checked_realloc_group!(CheckedReallocMut : ReallocMut 
        { [mut] checked_realloc_mut => realloc_mut, [mut] checked_rezalloc_mut => rezalloc_mut });
}
