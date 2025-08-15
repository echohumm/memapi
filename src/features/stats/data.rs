use crate::{
    stats::AllocRes::{Fail, Succ},
    AllocPattern,
};
use alloc::{alloc::Layout, string::ToString};
use core::{
    fmt::{self, Display, Formatter},
    hint::unreachable_unchecked,
    ptr::NonNull,
};

/// The result of an allocation operation, containing statistics on the operation.
#[derive(Debug)]
pub enum AllocRes {
    /// The allocation succeeded.
    Succ(AllocStat),
    /// The allocation failed.
    Fail(AllocStat),
}

impl Display for AllocRes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Succ(stat) => match stat {
                AllocStat::Alloc {
                    region,
                    kind,
                    total,
                } => {
                    write!(
                        f,
                        "Successful initial allocation of {} bytes with alignment {} at {:p}, and \
                        newly allocated bytes being {}. ({} total bytes allocated)",
                        region.size,
                        region.align,
                        region.ptr,
                        match kind {
                            AllocPattern::Uninitialized => "uninitialized".to_string(),
                            AllocPattern::Zeroed => "zeroed".to_string(),
                            #[cfg(feature = "alloc_ext")]
                            AllocPattern::Filled(n) => alloc::format!("filled with the byte {}", n),
                            // SAFETY: Only a reallocation can be a shrink, not an allocation.
                            AllocPattern::Shrink => unsafe { unreachable_unchecked() },
                        },
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
                                "newly allocated bytes were uninitialized".to_string(),
                            AllocPattern::Zeroed => "newly allocated bytes were zeroed".to_string(),
                            #[cfg(feature = "alloc_ext")]
                            AllocPattern::Filled(n) => alloc::format!(
                                "newly allocated bytes were filled with the byte {}",
                                n
                            ),
                            AllocPattern::Shrink =>
                                "there were no newly allocated bytes".to_string(),
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
                #[cfg(feature = "fallible_dealloc")]
                AllocStat::TryFree { region, total, .. } => {
                    write!(
                        f,
                        "Successful fallible deallocation of {} bytes with alignment {} at \
					{:p}. ({} total bytes allocated)",
                        region.size, region.align, region.ptr, total
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
                #[cfg(feature = "fallible_dealloc")]
                AllocStat::TryFree {
                    status,
                    region,
                    total,
                } => {
                    write!(
                        f,
                        "Failed fallible deallocation of {} bytes with alignment {} at {:p}. \
						({} total bytes allocated). Block status: {}",
                        region.size, region.align, region.ptr, total, status
                    )
                }
            },
        }
    }
}

/// A loggable allocation statistic.
#[derive(Debug)]
pub enum AllocStat {
    /// An allocation operation.
    Alloc {
        /// The memory region that was allocated.
        region: MemoryRegion,
        /// The kind of allocation.
        kind: AllocPattern,
        /// The total number of bytes allocated after this call.
        total: usize,
    },
    /// A reallocation (resizing) operation.
    Realloc {
        /// The old and new memory regions' information.
        info: ResizeMemRegions,
        /// The kind of allocation.
        kind: AllocPattern,
        /// The total number of bytes allocated after this call.
        total: usize,
    },
    /// A deallocation operation.
    Free {
        /// The memory region that was freed.
        region: MemoryRegion,
        /// The total number of bytes allocated after this call.
        total: usize,
    },
    #[cfg(feature = "fallible_dealloc")]
    /// A fallible deallocation operation.
    TryFree {
        /// The block status of the memory region.
        status: crate::fallible_dealloc::BlockStatus,
        /// The memory region that was freed.
        region: MemoryRegion,
        /// The total number of bytes allocated after this call.
        total: usize,
    },
}

impl AllocStat {
    pub(crate) fn new_realloc(
        old_ptr: NonNull<u8>,
        new_ptr: *mut u8,
        old_layout: Layout,
        new_layout: Layout,
        kind: AllocPattern,
        total: usize,
    ) -> AllocStat {
        AllocStat::Realloc {
            info: ResizeMemRegions {
                old: MemoryRegion {
                    ptr: old_ptr.as_ptr(),
                    size: old_layout.size(),
                    align: old_layout.align(),
                },
                new: MemoryRegion {
                    ptr: new_ptr,
                    size: new_layout.size(),
                    align: new_layout.align(),
                },
            },
            kind,
            total,
        }
    }
}

/// A contiguous region of memory.
#[derive(Debug)]
pub struct MemoryRegion {
    /// Pointer to the start of the region.
    pub ptr: *mut u8,
    /// Size of the region in bytes.
    pub size: usize,
    /// Alignment the region was allocated with.
    pub align: usize,
}

/// Old vs. new regions when resizing.
#[derive(Debug)]
pub struct ResizeMemRegions {
    /// The original memory region.
    pub old: MemoryRegion,
    /// The new memory region.
    pub new: MemoryRegion,
}
