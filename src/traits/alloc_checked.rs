/// Variants corresponding to immutable traits, from [`crate::traits::alloc`].
pub mod alloc {
    use {
        crate::{
            error::Error,
            layout::Layout,
            prelude::{AllocDescriptor, AllocMut},
            traits::alloc::Dealloc
        },
        ::core::{
            ptr::{self, NonNull},
            result::Result::{self}
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
        /// - <code>Err([Error::Unsupported])</code> if checked deallocation is unsupported. TODO:
        ///   in this case ...
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
}

/// Variants corresponding to mutable traits, from [`crate::traits::alloc_mut`].
pub mod alloc_mut {
    use {
        crate::{
            error::Error,
            layout::Layout,
            prelude::{AllocDescriptor, AllocMut},
            traits::alloc_mut::DeallocMut
        },
        ::core::{
            ptr::{self, NonNull},
            result::Result::{self}
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
}

// TODO: grow, shrink, realloc vers. ?
