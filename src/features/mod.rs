#[cfg(feature = "alloc_ext")]
/// Allocator abstractions.
pub mod alloc_ext;
#[cfg(feature = "alloc_slice")]
/// Slice-specific allocator abstractions.
pub mod alloc_slice;
#[cfg(feature = "resize_in_place")]
/// Reallocation in-place.
pub mod in_place;

#[cfg(feature = "owned")]
/// Owned data types.
pub mod owned;
#[cfg(feature = "stats")]
/// Allocation statistic gathering and reporting.
pub mod stats;
