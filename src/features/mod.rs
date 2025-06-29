#[cfg(feature = "alloc_ext")]
/// Allocator abstractions.
pub mod alloc_ext;
#[cfg(feature = "resize_in_place")]
/// Reallocation in-place.
pub mod in_place;

#[cfg(feature = "stats")]
/// Allocation statistic gathering and reporting.
pub mod stats;
#[cfg(feature = "owned")]
/// An owned buffer type.
pub mod owned;
