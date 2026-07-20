use {
    ::bitflags::bitflags,
    ::core::{iter::Extend, num::NonZeroUsize, result::Result::Ok}
};

// TODO: properly combine sets of allocator trait features (like ZstCheckedDealloc and some others
//  are missing)

/// Trait defining the error type returned by an allocator.
///
/// This trait is shared between [`alloc`] and [`alloc_mut`]'s allocation traits.
pub trait AllocDescriptor {
    /// The error type returned by this allocator.
    type Error: ::core::convert::From<crate::error::Error>
        + ::core::fmt::Debug
        + ::core::fmt::Display;

    /// Bitflags for the allocator's supported features.
    const FEATURES: AllocFeatures = AllocFeatures::DEALLOC.union(AllocFeatures::REALLOC);

    /// The minimum alignment returned by all allocation calls made to this allocator.
    // SAFETY: 1 is non-zero and the lowest valid alignment.
    const MIN_ALIGN: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(1) };

    /// Returns whether this allocator supports the featureset represented by the provided bitflags.
    #[must_use]
    fn supports(features: AllocFeatures) -> bool {
        Self::FEATURES.contains(features)
    }
}

bitflags! {
    /// Bitflags for features supported by an allocator.
    #[repr(transparent)]
    pub struct AllocFeatures: u16 {
        /// Supports [deallocation](alloc::Dealloc::dealloc).
        const DEALLOC = 1 << 0;
        /// Supports [reallocation](alloc::Realloc::realloc).
        const REALLOC = 1 << 1;

        /// Supports checked deallocation (implies [`DEALLOC`](AllocFeatures::DEALLOC)).
        const CHECKED_DEALLOC = 1 << 2 | AllocFeatures::DEALLOC.bits();
        /// Supports checked resizing of allocations (implies [`REALLOC`](AllocFeatures::REALLOC)).
        const CHECKED_REALLOC = 1 << 3 | AllocFeatures::REALLOC.bits();
    }
}

/// The primary allocation traits. These depend on the [`alloc_mut`] traits.
pub mod alloc;

/// Mutable allocation traits.
///
/// These are automatically implemented for <code>A: [Alloc](alloc::Alloc)</code>, so you only need
/// to implement them if your allocator requires mutable access to perform operations.
///
/// Due to this, they are also broader than the [`alloc`] traits.
pub mod alloc_mut;

#[cfg(feature = "alloc_checked_trait")]
/// Traits containing checked versions of unsafe allocation functions, which *must* return an error
/// if passed an invalid argument instead of causing undefined behavior.
pub mod alloc_checked;

#[cfg(feature = "alloc_temp_trait")]
/// A trait for scoped allocation, like C's `alloca`.
pub mod alloc_temp;

/// Stateless allocation traits.
///
/// These mirror the [`alloc`] traits, but their operations are associated functions taking no
/// `self`, for allocators which carry no internal state (e.g. zero-sized allocators backed by a
/// global or a static).
#[cfg(feature = "zst_alloc_trait")]
pub mod zst_alloc;

/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

#[doc(hidden)] pub mod helpers;
