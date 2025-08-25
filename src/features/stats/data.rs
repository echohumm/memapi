#![allow(clippy::match_same_arms)]
use {
    crate::{
        AllocPattern,
        Layout,
        stats::AllocRes::{Fail, Succ}
    },
    core::{
        fmt::{self, Display, Formatter},
        hint::unreachable_unchecked,
        ptr::NonNull
    }
};

/// The result of an allocation operation, containing statistics on the operation.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum AllocRes {
    /// The allocation succeeded.
    Succ(AllocStat),
    /// The allocation failed.
    Fail(AllocStat)
}

fn alloc_kind_str(kind: AllocPattern) -> &'static str {
    match kind {
        AllocPattern::Uninitialized => "uninitialized",
        AllocPattern::Zeroed => "zeroed",
        #[cfg(feature = "alloc_ext")]
        // SAFETY: we map Fill to Uninitialized
        AllocPattern::Filled(_) => unsafe { unreachable_unchecked() },
        // SAFETY: only realloc can shrink, not alloc
        AllocPattern::Shrink => unsafe { unreachable_unchecked() }
    }
}

impl Display for AllocRes {
    // its long, but simple so we dont care
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Succ(stat) => match stat {
                AllocStat::Alloc { region, kind, total } => {
                    write!(
                        f,
                        "Successful initial allocation of {} bytes with alignment {} at {:p}, and \
                         newly allocated bytes being {}. ({} total bytes allocated)",
                        region.size,
                        region.align,
                        region.ptr,
                        alloc_kind_str(*kind),
                        total
                    )
                }
                AllocStat::Realloc { info, kind, total } => {
                    write!(
                        f,
                        "Successful reallocation from {}->{} bytes with alignment {}->{}. \
                         Allocation moved {:p}->{:p} and {}. ({} total bytes allocated)",
                        info.old.size,
                        info.new.size,
                        info.old.align,
                        info.new.align,
                        info.old.ptr,
                        info.new.ptr,
                        match kind {
                            AllocPattern::Uninitialized =>
                                "newly allocated bytes were uninitialized",
                            AllocPattern::Zeroed => "newly allocated bytes were zeroed",
                            #[cfg(feature = "alloc_ext")]
                            // SAFETY: we map Fill to Uninitialized
                            AllocPattern::Filled(_) => unsafe { unreachable_unchecked() },
                            AllocPattern::Shrink => "there were no newly allocated bytes"
                        },
                        total
                    )
                }
                AllocStat::Free { region, total } => {
                    write!(
                        f,
                        "Deallocation of {} bytes with alignment {} at {:p}. ({} total bytes \
                         allocated)",
                        region.size, region.align, region.ptr, total
                    )
                }
                #[cfg(feature = "checked_dealloc")]
                AllocStat::TryFree { region, total, .. } => {
                    write!(
                        f,
                        "Successful fallible deallocation of {} bytes with alignment {} at {:p}. \
                         ({} total bytes allocated)",
                        region.size, region.align, region.ptr, total
                    )
                }
                // TODO: use effective_layout
                #[cfg(feature = "alloc_aligned_at")]
                AllocStat::AllocAlignedAt { region, offset, kind, total, .. } => {
                    write!(
                        f,
                        "Successful offset-aligned allocation of {} bytes with alignment {} at \
                         {:p}+{} and {}. ({} total bytes allocated)",
                        region.size,
                        region.align,
                        region.ptr,
                        offset,
                        alloc_kind_str(*kind),
                        total
                    )
                }
            },

            Fail(stat) => match stat {
                AllocStat::Alloc { region, .. } => {
                    write!(
                        f,
                        "Failed initial allocation of {} bytes with alignment {}.",
                        region.size, region.align
                    )
                }
                AllocStat::Realloc { info, .. } => {
                    write!(
                        f,
                        "Failed reallocation from {}->{} bytes with alignment {}->{}. Original \
                         allocation at {:p}.",
                        info.old.size, info.new.size, info.old.align, info.new.align, info.old.ptr
                    )
                }
                // SAFETY: free is "infallible"
                AllocStat::Free { .. } => unsafe { unreachable_unchecked() },
                #[cfg(feature = "checked_dealloc")]
                AllocStat::TryFree { status, region, total } => {
                    write!(
                        f,
                        "Failed fallible deallocation of {} bytes with alignment {} at {:p}. ({} \
                         total bytes allocated). Block status: {}",
                        region.size, region.align, region.ptr, total, status
                    )
                }
                #[cfg(feature = "alloc_aligned_at")]
                AllocStat::AllocAlignedAt { region, offset, .. } => {
                    write!(
                        f,
                        "Failed offset-aligned allocation of {} bytes with alignment {} at offset \
                         {}",
                        region.size, region.align, offset,
                    )
                }
            }
        }
    }
}

/// A loggable allocation statistic.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum AllocStat {
    /// An allocation operation.
    Alloc {
        /// The memory region that was allocated.
        region: MemoryRegion,
        /// The kind of allocation.
        kind: AllocPattern,
        /// The total number of bytes allocated after this call.
        total: usize
    },
    /// A reallocation (resizing) operation.
    Realloc {
        /// The old and new memory regions' information.
        info: ResizeMemRegions,
        /// The kind of allocation.
        kind: AllocPattern,
        /// The total number of bytes allocated after this call.
        total: usize
    },
    /// A deallocation operation.
    Free {
        /// The memory region that was freed.
        region: MemoryRegion,
        /// The total number of bytes allocated after this call.
        total: usize
    },
    #[cfg(feature = "checked_dealloc")]
    /// A fallible deallocation operation.
    TryFree {
        /// The block status of the memory region.
        status: crate::checked_dealloc::BlockStatus,
        /// The memory region that was freed.
        region: MemoryRegion,
        /// The total number of bytes allocated after this call.
        total: usize
    },
    #[cfg(feature = "alloc_aligned_at")]
    /// An offset-aligned allocation operation.
    AllocAlignedAt {
        /// The memory region that was allocated.
        region: MemoryRegion,
        /// The offset after which the allocation is aligned.
        offset: usize,
        /// The effective layout of the allocation.
        effective_layout: Layout,
        /// The kind of allocation.
        kind: AllocPattern,
        /// The total number of bytes allocated after this call.
        total: usize
    }
}

impl AllocStat {
    pub(crate) const fn new_realloc(
        old_ptr: NonNull<u8>,
        new_ptr: *mut u8,
        old_layout: Layout,
        new_layout: Layout,
        kind: AllocPattern,
        total: usize
    ) -> AllocStat {
        AllocStat::Realloc {
            info: ResizeMemRegions {
                old: MemoryRegion {
                    ptr: old_ptr.as_ptr(),
                    size: old_layout.size(),
                    align: old_layout.align()
                },
                new: MemoryRegion {
                    ptr: new_ptr,
                    size: new_layout.size(),
                    align: new_layout.align()
                }
            },
            #[cfg(feature = "alloc_ext")]
            kind: match kind {
                AllocPattern::Filled(_) => AllocPattern::Uninitialized,
                other => other
            },
            #[cfg(not(feature = "alloc_ext"))]
            kind,
            total
        }
    }
}

/// A contiguous region of memory.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct MemoryRegion {
    /// Pointer to the start of the region.
    pub ptr: *mut u8,
    /// Size of the region in bytes.
    pub size: usize,
    /// Alignment the region was allocated with.
    pub align: usize
}

/// The old and new regions of a resize operation.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct ResizeMemRegions {
    /// The original memory region.
    pub old: MemoryRegion,
    /// The new memory region.
    pub new: MemoryRegion
}
