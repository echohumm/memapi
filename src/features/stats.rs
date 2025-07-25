#![allow(unused_qualifications)]

use crate::{
    stats::AllocRes::{Fail, Succ},
    Alloc, AllocError, DefaultAlloc,
};
use alloc::{alloc::Layout, format, string::ToString};
use core::{
    fmt::{self, Display, Formatter},
    ptr::{null_mut, NonNull},
    sync::atomic::{
        AtomicUsize,
        Ordering::{Acquire, Release},
    },
};

/// A wrapper that delegates all `Alloc` calls to `A` and logs
/// each result via `L`.
pub struct Stats<A, L: StatsLogger>(pub A, pub L);

impl<L: StatsLogger> Stats<DefaultAlloc, L> {
    /// Create a new stats‐collecting allocator wrapper.
    pub const fn new(logger: L) -> Stats<DefaultAlloc, L> {
        Stats(DefaultAlloc, logger)
    }
}

impl<A, L: StatsLogger> Stats<A, L> {
    /// Create a new stats‐collecting allocator wrapper.
    pub const fn new_in(inner: A, logger: L) -> Stats<A, L> {
        Stats(inner, logger)
    }
}

// no-op logger
impl StatsLogger for () {
    fn log(&self, _: AllocRes) {}
    fn inc_total_bytes_allocated(&self, _: usize) -> usize {
        0
    }
    fn dec_total_bytes_allocated(&self, _: usize) -> usize {
        0
    }
    fn total(&self) -> usize {
        0
    }
}

macro_rules! atomic_total_ops {
    ($this:expr $(, $field:ident)?) => {
            #[inline]
            fn inc_total_bytes_allocated(&self, bytes: usize) -> usize {
                let res = self$(.$field)?.load(Acquire) + bytes;
                self$(.$field)?.store(res, Release);
                res
            }

            #[inline]
            fn dec_total_bytes_allocated(&self, bytes: usize) -> usize {
                let res = self$(.$field)?.load(Acquire) - bytes;
                self$(.$field)?.store(res, Release);
                res
            }

            #[inline]
            fn total(&self) -> usize {
                self$(.$field)?.load(Acquire)
            }
    };
}

// byte counter-only logger (no stat)
impl StatsLogger for AtomicUsize {
    fn log(&self, _: AllocRes) {}

    atomic_total_ops!(self);
}

#[cfg(feature = "std")]
// file stat-only logger (no byte-count)
impl StatsLogger for std::sync::Mutex<std::fs::File> {
    fn log(&self, stat: AllocRes) {
        <std::fs::File as std::io::Write>::write_all(
            &mut self.lock().expect("`Mutex<File>` was poisoned"),
            format!("{stat}").as_bytes(),
        )
        .expect("failed to write to `File`");
    }
    fn inc_total_bytes_allocated(&self, _: usize) -> usize {
        0
    }
    fn dec_total_bytes_allocated(&self, _: usize) -> usize {
        0
    }
    fn total(&self) -> usize {
        0
    }
}

/// Delegate all calls to the inner logger.
macro_rules! delegate_logger {
    ($ty:ty) => {
        impl<L: StatsLogger + ?Sized> StatsLogger for $ty {
            fn log(&self, stat: AllocRes) {
                (**self).log(stat)
            }
            fn inc_total_bytes_allocated(&self, bytes: usize) -> usize {
                (**self).inc_total_bytes_allocated(bytes)
            }
            fn dec_total_bytes_allocated(&self, bytes: usize) -> usize {
                (**self).dec_total_bytes_allocated(bytes)
            }
            fn total(&self) -> usize {
                (**self).total()
            }
        }
    };
}

delegate_logger!(&L);
delegate_logger!(&mut L);
delegate_logger!(alloc::boxed::Box<L>);
delegate_logger!(alloc::rc::Rc<L>);
delegate_logger!(alloc::sync::Arc<L>);

#[cfg(feature = "std")]
/// An IO buffer that can be used to log statistics.
pub struct IOLog<W: std::io::Write> {
    /// The writer to log to.
    pub buf: std::sync::Mutex<W>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize,
}

#[cfg(feature = "std")]
/// A buffer that can be used to log statistics.
pub struct FmtLog<W: fmt::Write> {
    /// The writer to log to.
    pub buf: std::sync::Mutex<W>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize,
}

#[cfg(feature = "std")]
/// A logger that pushes all statistics to a vector.
pub struct StatCollectingLog {
    // maybe i should use crate::owned::OwnedBuf here
    /// The vector which results are passed to.
    pub results: std::sync::Mutex<Vec<AllocRes>>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize,
}

#[cfg(feature = "std")]
impl<W: std::io::Write> StatsLogger for IOLog<W> {
    #[inline]
    fn log(&self, stat: AllocRes) {
        self.buf
            .lock()
            .expect("inner `Mutex<W>` for `WrittenLog` was poisoned")
            .write_all(format!("{stat}\n").as_bytes())
            .expect("failed to write to inner `W` of `WrittenLog`");
    }

    atomic_total_ops!(self, total);
}

#[cfg(feature = "std")]
impl<W: fmt::Write> StatsLogger for FmtLog<W> {
    #[inline]
    fn log(&self, stat: AllocRes) {
        self.buf
            .lock()
            .expect("inner `Mutex<W>` for `FmtLog` was poisoned")
            .write_fmt(format_args!("{stat}\n"))
            .expect("failed to write to inner `W` of `FmtLog`");
    }

    atomic_total_ops!(self, total);
}

#[cfg(feature = "std")]
impl StatsLogger for StatCollectingLog {
    #[inline]
    fn log(&self, stat: AllocRes) {
        self.results
            .lock()
            .expect("inner `Mutex<Vec<AllocRes>>` for `StatCollectingLog` was poisoned")
            .push(stat);
    }

    atomic_total_ops!(self, total);
}

#[cfg(feature = "std")]
impl Default for IOLog<std::io::Stdout> {
    fn default() -> IOLog<std::io::Stdout> {
        IOLog {
            buf: std::sync::Mutex::new(std::io::stdout()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl Default for IOLog<std::fs::File> {
    fn default() -> IOLog<std::fs::File> {
        IOLog {
            buf: std::sync::Mutex::new(std::fs::File::create("alloc_stats.log").unwrap()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl<W: fmt::Write + Default> Default for FmtLog<W> {
    fn default() -> FmtLog<W> {
        FmtLog {
            buf: std::sync::Mutex::new(W::default()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl Default for StatCollectingLog {
    fn default() -> StatCollectingLog {
        StatCollectingLog {
            results: std::sync::Mutex::new(Vec::new()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl<W: std::io::Write> From<W> for IOLog<W> {
    #[inline]
    fn from(w: W) -> IOLog<W> {
        IOLog::new(w)
    }
}

#[cfg(feature = "std")]
impl<W: fmt::Write> From<W> for FmtLog<W> {
    fn from(w: W) -> FmtLog<W> {
        FmtLog::new(w)
    }
}

#[cfg(feature = "std")]
impl<W: std::io::Write> IOLog<W> {
    /// Creates a new [`IOLog`] from a writer.
    #[inline]
    pub const fn new(buf: W) -> IOLog<W> {
        IOLog {
            buf: std::sync::Mutex::new(buf),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl<W: fmt::Write> FmtLog<W> {
    /// Creates a new [`FmtLog`] from a writer.
    #[inline]
    pub const fn new(buf: W) -> FmtLog<W> {
        FmtLog {
            buf: std::sync::Mutex::new(buf),
            total: AtomicUsize::new(0),
        }
    }

    /// Gets a reference to the log.
    ///
    /// # Panics
    ///
    /// This function will panic if the inner [`Mutex`](std::sync::Mutex) is poisoned.
    #[inline]
    pub fn get_log(&self) -> std::sync::MutexGuard<'_, W> {
        self.buf
            .lock()
            .expect("inner `Mutex<W>` for `FmtLog` was poisoned")
    }
}

#[cfg(feature = "std")]
impl StatCollectingLog {
    /// Creates a new [`StatCollectingLog`].
    #[must_use]
    #[inline]
    pub const fn new() -> StatCollectingLog {
        StatCollectingLog {
            results: std::sync::Mutex::new(Vec::new()),
            total: AtomicUsize::new(0),
        }
    }

    /// Creates a new [`StatCollectingLog`] with the given capacity.
    #[must_use]
    #[inline]
    pub fn with_capacity(cap: usize) -> StatCollectingLog {
        StatCollectingLog {
            results: std::sync::Mutex::new(Vec::with_capacity(cap)),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
/// A logger that writes to a file.
pub type FileLog = IOLog<std::fs::File>;

#[cfg(feature = "std")]
/// A logger that writes to stdout.
pub type StdoutLog = IOLog<std::io::Stdout>;

#[cfg(feature = "std")]
/// A logger that writes to a string.
pub type StringLog = FmtLog<String>;

#[cfg(feature = "std")]
/// A logger that writes to a string slice.
pub type StrLog<'s> = FmtLog<&'s str>;

/// Trait for logging statistics.
///
/// This requires that `Self` allows safe mutable access via an immutable reference, such as the
/// std-only `IOLog` struct:
///
/// ```rust,no_run
/// # use std::{
/// #    sync::{
/// #        Mutex,
/// #        atomic::AtomicUsize,
/// #    },
/// #    fs::File,
/// #    io::Write,
/// # };
///
/// pub struct IOLog<W: Write> {
///     // allows mutation through an immutable reference via lock() method
///     buf: Mutex<W>,
///     // allows mutation through an immutable reference via atomic operations
///     total: AtomicUsize,
/// }
/// ```
pub trait StatsLogger {
    /// Logs a statistic.
    fn log(&self, stat: AllocRes);

    /// Increments the total bytes allocated and returns the new value.
    fn inc_total_bytes_allocated(&self, bytes: usize) -> usize;
    /// Decrements the total bytes allocated and returns the new value.
    fn dec_total_bytes_allocated(&self, bytes: usize) -> usize;

    /// Returns the total number of bytes allocated.
    fn total(&self) -> usize;
}

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
                        newly allocated bytes being {}. ({total} total bytes allocated)",
                        region.size,
                        region.align,
                        region.ptr,
                        match kind {
                            AllocKind::Uninitialized => "uninitialized".to_string(),
                            AllocKind::Zeroed => "zeroed".to_string(),
                            AllocKind::Filled(n) => format!("filled with the byte {n}"),
                            AllocKind::Patterned => "filled with a pattern".to_string(),
                            AllocKind::Shrink => unsafe { core::hint::unreachable_unchecked() },
                        }
                    )
                }
                AllocStat::Realloc { info, kind, total } => {
                    write!(
                        f,
                        "Successful reallocation from {}->{} bytes with alignment {}->{}. \
                        Allocation moved {:p}->{:p} and {}. ({total} total bytes allocated)",
                        info.old.size,
                        info.new.size,
                        info.old.align,
                        info.new.align,
                        info.old.ptr,
                        info.new.ptr,
                        match kind {
                            AllocKind::Uninitialized =>
                                "newly allocated bytes were uninitialized".to_string(),
                            AllocKind::Zeroed => "newly allocated bytes were zeroed".to_string(),
                            AllocKind::Filled(n) =>
                                format!("newly allocated bytes were filled with the byte {n}"),
                            AllocKind::Patterned =>
                                "newly allocated bytes were filled with a pattern".to_string(),
                            AllocKind::Shrink => "there were no newly allocated bytes".to_string(),
                        }
                    )
                }
                AllocStat::Free { region, total } => {
                    write!(
                        f,
                        "Deallocation of {} bytes with alignment {} at {:p}. ({total} total bytes \
                        allocated)",
                        region.size, region.align, region.ptr
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
                // free is "infallible"
                AllocStat::Free { .. } => unsafe { core::hint::unreachable_unchecked() },
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
        kind: AllocKind,
        /// The total number of bytes allocated currently.
        total: usize,
    },
    /// A reallocation (resizing) operation.
    Realloc {
        /// The old and new memory regions' info.
        info: ResizeInfo,
        /// The kind of allocation.       
        kind: AllocKind,
        /// The total number of bytes allocated currently.
        total: usize,
    },
    /// A deallocation operation.
    Free {
        /// The memory region that was freed.
        region: MemoryRegion,
        /// The total number of bytes allocated currently.
        total: usize,
    },
}

impl AllocStat {
    fn new_realloc(
        old_ptr: NonNull<u8>,
        new_ptr: *mut u8,
        old_layout: Layout,
        new_layout: Layout,
        kind: AllocKind,
        total: usize,
    ) -> AllocStat {
        AllocStat::Realloc {
            info: ResizeInfo {
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
pub struct ResizeInfo {
    /// The original memory region.
    pub old: MemoryRegion,
    /// The new memory region.
    pub new: MemoryRegion,
}

/// What kind of allocation operation happened.
#[derive(Debug)]
pub enum AllocKind {
    /// New bytes were not filled and are uninitialized.
    Uninitialized,
    /// New bytes were zeroed.
    Zeroed,
    /// New bytes were filled with a constant value.
    Filled(u8),
    /// New bytes were filled with a pattern.
    // dontfixme: contain the pattern
    // why though, me? why the hell would we contain the pattern??
    // for anyone reading this, yes i am going insane.
    Patterned,
    /// There were no new bytes.
    Shrink,
}

#[track_caller]
#[inline]
fn allocate<A: Alloc, L: StatsLogger, F: Fn(&A, Layout) -> Result<NonNull<u8>, AllocError>>(
    slf: &Stats<A, L>,
    allocate: F,
    layout: Layout,
    kind: AllocKind,
) -> Result<NonNull<u8>, AllocError> {
    let size = layout.size();
    match allocate(&slf.0, layout) {
        Ok(ptr) => {
            let total = slf.1.inc_total_bytes_allocated(size);
            slf.1.log(Succ(AllocStat::Alloc {
                region: MemoryRegion {
                    ptr: ptr.as_ptr(),
                    size,
                    align: layout.align(),
                },
                kind,
                total,
            }));
            Ok(ptr)
        }
        Err(e) => {
            slf.1.log(Fail(AllocStat::Alloc {
                region: MemoryRegion {
                    ptr: null_mut(),
                    size,
                    align: layout.align(),
                },
                kind,
                total: slf.1.total(),
            }));
            Err(e)
        }
    }
}

#[track_caller]
#[inline]
fn grow<
    A: Alloc,
    L: StatsLogger,
    F: Fn(&A, NonNull<u8>, Layout, Layout) -> Result<NonNull<u8>, AllocError>,
>(
    slf: &Stats<A, L>,
    grow: F,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    kind: AllocKind,
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
                total,
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
                slf.1.total(),
            )));
            Err(e)
        }
    }
}

impl<A: Alloc, L: StatsLogger> Alloc for Stats<A, L> {
    #[track_caller]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        allocate(self, A::alloc, layout, AllocKind::Uninitialized)
    }

    #[track_caller]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        allocate(self, A::alloc_zeroed, layout, AllocKind::Zeroed)
    }

    #[track_caller]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        self.0.dealloc(ptr, layout);

        let size = layout.size();
        let total = self.1.dec_total_bytes_allocated(size);
        self.1.log(Succ(AllocStat::Free {
            region: MemoryRegion {
                ptr: ptr.as_ptr(),
                size,
                align: layout.align(),
            },
            total,
        }));
    }

    #[track_caller]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            |a, ptr, old, new| a.grow(ptr, old, new),
            ptr,
            old_layout,
            new_layout,
            AllocKind::Uninitialized,
        )
    }

    #[track_caller]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            |a, ptr, old, new| a.grow_zeroed(ptr, old, new),
            ptr,
            old_layout,
            new_layout,
            AllocKind::Zeroed,
        )
    }

    #[track_caller]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
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
                    AllocKind::Shrink,
                    total,
                )));
                Ok(new_ptr)
            }
            Err(e) => {
                self.1.log(Fail(AllocStat::new_realloc(
                    ptr,
                    null_mut(),
                    old_layout,
                    new_layout,
                    AllocKind::Shrink,
                    self.1.total(),
                )));
                Err(e)
            }
        }
    }
}
