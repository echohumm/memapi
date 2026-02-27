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
    const FEATURES: AllocFeatures;
}

bitflags! {
    /// Bitflags for features supported by an allocator.
    #[repr(transparent)]
    pub struct AllocFeatures: u8 {
        /// Supports [deallocation](alloc::Dealloc::dealloc).
        const DEALLOC = 0b0000_0001;
        /// Supports [growing allocations](alloc::Grow::grow).
        const GROW = 0b0000_0010;
        /// Supports [shrinking allocations](alloc::Shrink::shrink).
        const SHRINK = 0b0000_0100;
        /// Supports realloc (implies [`GROW`](AllocFeatures::GROW) and
        /// [`SHRINK`](AllocFeatures::SHRINK)).
        const REALLOC = 0b0000_1000 | AllocFeatures::GROW.bits() | AllocFeatures::SHRINK.bits();

        /// Supports checked deallocation (implies DEALLOC).
        const CHECKED_DEALLOC = 0b0001_0000 | AllocFeatures::DEALLOC.bits();
        /// Supports checked growth of allocations (implies [`GROW`](AllocFeatures::GROW)).
        const CHECKED_GROW = 0b0010_0000 | AllocFeatures::GROW.bits();
        /// Supports checked shrinking of allocations (implies [`SHRINK`](AllocFeatures::SHRINK)).
        const CHECKED_SHRINK = 0b0100_0000 | AllocFeatures::SHRINK.bits();
        /// Supports checked resizing of allocations (implies [`REALLOC`](AllocFeatures::REALLOC),
        /// [`CHECKED_GROW`](AllocFeatures::CHECKED_GROW), and
        /// [`CHECKED_SHRINK`](AllocFeatures::CHECKED_SHRINK)).
        const CHECKED_REALLOC = 0b1000_0000
            | AllocFeatures::REALLOC.bits()
            | AllocFeatures::CHECKED_GROW.bits()
            | AllocFeatures::CHECKED_SHRINK.bits();
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

#[cfg(feature = "checked_ops")] pub mod alloc_checked;

#[cfg(feature = "alloc_temp_trait")]
/// A trait for scoped allocation, like C's `alloca`.
pub mod alloc_temp;

/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

#[doc(hidden)] pub mod helpers;
