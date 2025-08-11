#[cfg(feature = "alloc_ext")]
/// Allocator abstractions.
pub(crate) mod alloc_ext;
#[cfg(feature = "alloc_slice")]
/// Slice-specific allocator abstractions.
pub(crate) mod alloc_slice;
#[cfg(feature = "resize_in_place")]
/// Reallocation in-place.
pub(crate) mod resize_in_place;

#[cfg(feature = "stats")]
/// Allocation statistic gathering and reporting.
pub mod stats;

#[cfg(feature = "fallible_dealloc")]
/// Fallible deallocation.
pub mod fallible_dealloc;
