use {
    crate::{
        Alloc,
        AllocPattern,
        DefaultAlloc,
        Layout,
        error::AllocError,
        stats::AllocRes::{Fail, Succ}
    },
    core::ptr::{NonNull, null_mut}
};

mod stat_logger;
pub use stat_logger::*;

mod data;
pub use data::*;

#[cfg(feature = "stats_thread_safe_io")] mod lock;
#[cfg(feature = "stats_thread_safe_io")] pub use lock::*;

pub(crate) mod minstring;

/// A wrapper that delegates all `Alloc` calls to `A` and logs
/// each result via `L`.
pub struct Stats<A, L: StatsLogger>(pub A, pub L);

impl<L: StatsLogger> Stats<DefaultAlloc, L> {
    const_if! {
        "const_extras",
        "Create a new stats‐collecting allocator wrapper.",
        #[inline]
        pub const fn new(logger: L) -> Stats<DefaultAlloc, L> {
            Stats(DefaultAlloc, logger)
        }
    }
}

impl<A, L: StatsLogger> Stats<A, L> {
    const_if! {
        "const_extras",
        "Create a new stats‐collecting allocator wrapper.",
        #[inline]
        pub const fn new_in(inner: A, logger: L) -> Stats<A, L> {
            Stats(inner, logger)
        }
    }
}

#[track_caller]
fn allocate<A: Alloc, L: StatsLogger, F: Fn(&A, Layout) -> Result<NonNull<u8>, AllocError>>(
    slf: &Stats<A, L>,
    allocate: F,
    layout: Layout,
    kind: AllocPattern
) -> Result<NonNull<u8>, AllocError> {
    let size = layout.size();
    match allocate(&slf.0, layout) {
        Ok(ptr) => {
            let total = slf.1.inc_total_bytes_allocated(size);
            slf.1.log(Succ(AllocStat::Alloc {
                region: MemoryRegion { ptr: ptr.as_ptr(), size, align: layout.align() },
                kind,
                total
            }));
            Ok(ptr)
        }
        Err(e) => {
            slf.1.log(Fail(AllocStat::Alloc {
                region: MemoryRegion { ptr: null_mut(), size, align: layout.align() },
                kind,
                total: slf.1.total()
            }));
            Err(e)
        }
    }
}

#[track_caller]
fn grow<
    A: Alloc,
    L: StatsLogger,
    F: Fn(&A, NonNull<u8>, Layout, Layout) -> Result<NonNull<u8>, AllocError>
>(
    slf: &Stats<A, L>,
    grow: F,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    kind: AllocPattern
) -> Result<NonNull<u8>, AllocError> {
    match grow(&slf.0, ptr, old_layout, new_layout) {
        Ok(new_ptr) => {
            let total = slf
                .1
                .inc_total_bytes_allocated(new_layout.size().saturating_sub(old_layout.size()));
            slf.1.log(Succ(AllocStat::new_realloc(
                ptr,
                new_ptr.as_ptr(),
                old_layout,
                new_layout,
                kind,
                total
            )));
            Ok(new_ptr)
        }
        Err(e) => {
            slf.1.log(Fail(AllocStat::new_realloc(
                ptr,
                null_mut(),
                old_layout,
                new_layout,
                kind,
                slf.1.total()
            )));
            Err(e)
        }
    }
}

impl<A: Alloc, L: StatsLogger> Alloc for Stats<A, L> {
    #[track_caller]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        allocate(self, A::alloc, layout, AllocPattern::Uninitialized)
    }

    #[track_caller]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        allocate(self, A::zalloc, layout, AllocPattern::Zeroed)
    }

    #[track_caller]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        self.0.dealloc(ptr, layout);

        let size = layout.size();
        let total = self.1.dec_total_bytes_allocated(size);
        self.1.log(Succ(AllocStat::Free {
            region: MemoryRegion { ptr: ptr.as_ptr(), size, align: layout.align() },
            total
        }));
    }

    #[track_caller]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            |a, ptr, old, new| a.grow(ptr, old, new),
            ptr,
            old_layout,
            new_layout,
            AllocPattern::Uninitialized
        )
    }

    #[track_caller]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            |a, ptr, old, new| a.zgrow(ptr, old, new),
            ptr,
            old_layout,
            new_layout,
            AllocPattern::Zeroed
        )
    }

    #[track_caller]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        match self.0.shrink(ptr, old_layout, new_layout) {
            Ok(new_ptr) => {
                let total = self
                    .1
                    .dec_total_bytes_allocated(old_layout.size().saturating_sub(new_layout.size()));
                self.1.log(Succ(AllocStat::new_realloc(
                    ptr,
                    new_ptr.as_ptr(),
                    old_layout,
                    new_layout,
                    AllocPattern::Shrink,
                    total
                )));
                Ok(new_ptr)
            }
            Err(e) => {
                self.1.log(Fail(AllocStat::new_realloc(
                    ptr,
                    null_mut(),
                    old_layout,
                    new_layout,
                    AllocPattern::Shrink,
                    self.1.total()
                )));
                Err(e)
            }
        }
    }
}

#[cfg(feature = "fallible_dealloc")]
#[cold]
#[inline(never)]
fn tryfree_err<A: Alloc, L: StatsLogger>(
    a: &Stats<A, L>,
    ptr: NonNull<u8>,
    layout: Layout,
    status: crate::fallible_dealloc::BlockStatus
) {
    a.1.log(Fail(AllocStat::TryFree {
        status,
        region: MemoryRegion { ptr: ptr.as_ptr(), size: layout.size(), align: layout.align() },
        total: a.1.total()
    }));
}

#[cfg(feature = "fallible_dealloc")]
impl<A: crate::fallible_dealloc::DeallocChecked, L: StatsLogger>
    crate::fallible_dealloc::DeallocChecked for Stats<A, L>
{
    fn try_dealloc(&self, ptr: NonNull<u8>, layout: Layout) -> Result<(), AllocError> {
        match self.0.try_dealloc(ptr, layout) {
            Ok(()) => {
                let size = layout.size();
                let total = self.1.dec_total_bytes_allocated(size);
                self.1.log(Succ(AllocStat::TryFree {
                    status: crate::fallible_dealloc::BlockStatus::Owned,
                    region: MemoryRegion { ptr: ptr.as_ptr(), size, align: layout.align() },
                    total
                }));
                Ok(())
            }
            Err(e) => {
                match e {
                    AllocError::DeallocFailed(p, l, ref c) => {
                        if let crate::error::Cause::InvalidBlockStatus(s) = c {
                            tryfree_err(self, p, l, *s);
                        } else {
                            tryfree_err(self, p, l, crate::fallible_dealloc::BlockStatus::Unknown);
                        }
                    }
                    _ => {
                        tryfree_err(
                            self,
                            ptr,
                            layout,
                            crate::fallible_dealloc::BlockStatus::Unknown
                        );
                    }
                }
                Err(e)
            }
        }
    }

    fn status(&self, ptr: NonNull<u8>, layout: Layout) -> crate::fallible_dealloc::BlockStatus {
        self.0.status(ptr, layout)
    }

    fn owns(&self, ptr: NonNull<u8>) -> bool { self.0.owns(ptr) }
}
