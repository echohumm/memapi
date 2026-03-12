use {
    ::bitflags::bitflags,
    ::core::{iter::Extend, result::Result::Ok}
};

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
        const CHECKED_DEALLOC = 1 << 4 | AllocFeatures::DEALLOC.bits();
        /// Supports checked resizing of allocations (implies [`REALLOC`](AllocFeatures::REALLOC)).
        const CHECKED_REALLOC = 1 << 5 | AllocFeatures::REALLOC.bits();
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

#[cfg(feature = "checked_ops")]
/// Traits containing checked versions of unsafe allocation functions, which *must* return an error
/// if passed an invalid argument instead of causing UB.
pub mod alloc_checked;

#[cfg(feature = "alloc_temp_trait")]
/// A trait for scoped allocation, like C's `alloca`.
pub mod alloc_temp;

/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

#[doc(hidden)] pub mod helpers;
