mod alloc;
pub use self::alloc::*;

#[cfg(feature = "alloc_mut_traits")] mod alloc_mut;
#[cfg(feature = "alloc_mut_traits")] pub use alloc_mut::*;

#[cfg(feature = "alloc_temp_trait")] mod alloc_temp;
#[cfg(feature = "alloc_temp_trait")] pub use alloc_temp::*;

/// Module for anything related specifically to data.
///
/// This includes marker traits, type properties, and miscellaneous data-handling traits.
pub mod data;

pub(super) mod helpers;
