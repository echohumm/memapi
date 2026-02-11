/// The primary allocation traits. These depend on the [`alloc_mut`] traits.
pub mod alloc;
pub use self::alloc::*;

/// Mutable allocation traits.
///
/// These are automatically implemented for <code>A: [Alloc]</code>, so you only need to implement
/// them if your allocator requires mutable access to perform operations.
///
/// Due to this, they are also broader than the [`alloc`] traits.
pub mod alloc_mut;

#[cfg(feature = "alloc_temp_trait")]
/// A trait for scoped allocation, like C's `alloca`.
pub mod alloc_temp;

/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

#[doc(hidden)] pub mod helpers;
