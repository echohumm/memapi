#[cfg(feature = "alloc_ext")]
/// Allocator abstractions.
pub(crate) mod alloc_ext;
#[cfg(feature = "alloc_slice")]
/// Slice-specific allocator abstractions.
pub(crate) mod alloc_slice;
#[cfg(feature = "resize_in_place")]
/// Reallocation in-place.
pub(crate) mod resize_in_place;

#[cfg(feature = "alloc_aligned_at")]
/// Allocation where the memory is only aligned after a given offset.
pub mod alloc_aligned_at;
#[cfg(feature = "checked_dealloc")]
/// Fallible deallocation.
pub mod checked_dealloc;
#[cfg(all(feature = "stats", any(not(feature = "no_alloc"), feature = "malloc_defaultalloc")))]
/// Allocation statistic gathering and reporting.
pub mod stats;
