use crate::{
    Alloc, AllocError,
    stats::AllocRes::{Fail, Succ},
};
use alloc::{alloc::Layout, boxed::Box, format, rc::Rc, string::ToString, sync::Arc};
use core::{
    fmt::{self, Display, Formatter},
    ptr::{NonNull, null_mut},
    sync::atomic::{
        AtomicUsize,
        Ordering::{Acquire, Release},
    },
};
#[cfg(feature = "std")]
use std::{
    fs::File,
    io::{Stdout, Write, stdout},
    sync::{Mutex, MutexGuard},
};

/// A wrapper that delegates all `Alloc` calls to `A` and logs
/// each result via `L`.
pub struct Stats<A, L: StatsLogger>(pub A, pub L);

impl<A, L: StatsLogger> Stats<A, L> {
    /// Create a new stats‐collecting allocator wrapper.
    pub const fn new(inner: A, logger: L) -> Self {
        Stats(inner, logger)
    }
}

// no-op logger
impl StatsLogger for () {
    fn log(&self, _stat: AllocRes) {}
    fn inc_total_bytes_allocated(&self, _bytes: usize) -> usize {
        0
    }
    fn dec_total_bytes_allocated(&self, _bytes: usize) -> usize {
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
    fn log(&self, _stat: AllocRes) {}

    atomic_total_ops!(self);
}

#[cfg(feature = "std")]
// file stat-only logger (no byte-count)
impl StatsLogger for Mutex<File> {
    fn log(&self, stat: AllocRes) {
        self.lock()
            .expect("`Mutex<File>` was poisoned")
            .write_all(format!("{stat}").as_bytes())
            .expect("failed to write to `File`");
    }
    fn inc_total_bytes_allocated(&self, _bytes: usize) -> usize {
        0
    }
    fn dec_total_bytes_allocated(&self, _bytes: usize) -> usize {
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
delegate_logger!(Box<L>);
delegate_logger!(Rc<L>);
delegate_logger!(Arc<L>);

#[cfg(feature = "std")]
/// An IO buffer that can be used to log statistics.
pub struct IOLog<W: Write> {
    /// The writer to log to.
    pub buf: Mutex<W>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize,
}

#[cfg(feature = "std")]
/// A buffer that can be used to log statistics.
pub struct FmtLog<W: fmt::Write> {
    /// The writer to log to.
    pub buf: Mutex<W>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize,
}

#[cfg(feature = "std")]
impl<W: Write> StatsLogger for IOLog<W> {
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
impl Default for IOLog<Stdout> {
    fn default() -> IOLog<Stdout> {
        IOLog {
            buf: Mutex::new(stdout()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl Default for IOLog<File> {
    fn default() -> IOLog<File> {
        IOLog {
            buf: Mutex::new(File::create("alloc_stats.log").unwrap()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl<W: fmt::Write + Default> Default for FmtLog<W> {
    fn default() -> FmtLog<W> {
        FmtLog {
            buf: Mutex::new(W::default()),
            total: AtomicUsize::new(0),
        }
    }
}

#[cfg(feature = "std")]
impl<W: Write> From<W> for IOLog<W> {
    #[inline]
    fn from(w: W) -> IOLog<W> {
        IOLog::new(w)
    }
}

#[cfg(feature = "std")]
impl<W: fmt::Write> From<W> for FmtLog<W> {
    fn from(w: W) -> Self {
        FmtLog::new(w)
    }
}

#[cfg(feature = "std")]
impl<W: Write> IOLog<W> {
    /// Creates a new [`IOLog`] from a writer.
    #[inline]
    pub const fn new(buf: W) -> IOLog<W> {
        IOLog {
            buf: Mutex::new(buf),
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
            buf: Mutex::new(buf),
            total: AtomicUsize::new(0),
        }
    }
    
    /// Gets a reference to the log.
    /// 
    /// # Panics
    /// 
    /// This function will panic if the inner [`Mutex`] is poisoned.
    #[inline]
    pub fn get_log(&self) -> MutexGuard<'_, W> {
        self.buf.lock().expect("inner `Mutex<W>` for `FmtLog` was poisoned")
    }
}

#[cfg(feature = "std")]
/// A logger that writes to a file.
pub type FileLog = IOLog<File>;

#[cfg(feature = "std")]
/// A logger that writes to stdout.
pub type StdoutLog = IOLog<Stdout>;

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
                        "Successful initial allocation of {} bytes with alignment {} at {:p}, and newly allocated bytes being {}. ({total} total bytes allocated)",
                        region.size,
                        region.align,
                        region.ptr,
                        match kind {
                            AllocKind::Uninitialized => "uninitialized".to_string(),
                            AllocKind::Zeroed => "zeroed".to_string(),
                            AllocKind::Filled(n) => format!("filled with the byte {n}"),
                            AllocKind::Patterned => "filled with a pattern".to_string(),
                            AllocKind::Shrink => unreachable!(),
                        }
                    )
                }
                AllocStat::Realloc { info, kind, total } => {
                    write!(
                        f,
                        "Successful reallocation from {}->{} bytes with alignment {}->{}. Allocation moved {:p}->{:p} and {}. ({total} total bytes allocated)",
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
                        "Deallocation of {} bytes with alignment {} at {:p}. ({total} total bytes allocated)",
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
                        "Failed reallocation from {}->{} bytes with alignment {}->{}. Original allocation at {:p}.",
                        info.old.size, info.new.size, info.old.align, info.new.align, info.old.ptr
                    )
                }
                // free is "infallible"
                AllocStat::Free { .. } => unreachable!(),
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
    // FIXME: return the pattern
    Patterned,
    /// There were no new bytes.
    Shrink,
}

impl<A: Alloc, L: StatsLogger> Alloc for Stats<A, L> {
    #[track_caller]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        let size = layout.size();
        match self.0.alloc(layout) {
            Ok(ptr) => {
                let total = self.1.inc_total_bytes_allocated(size);
                self.1.log(Succ(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: ptr.as_ptr(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Uninitialized,
                    total,
                }));
                Ok(ptr)
            }
            Err(e) => {
                self.1.log(Fail(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: null_mut(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Uninitialized,
                    total: self.1.total(),
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        let size = layout.size();
        match self.0.alloc_zeroed(layout) {
            Ok(ptr) => {
                let total = self.1.inc_total_bytes_allocated(size);
                self.1.log(Succ(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: ptr.as_ptr(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Zeroed,
                    total,
                }));
                Ok(ptr)
            }
            Err(e) => {
                self.1.log(Fail(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: null_mut(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Zeroed,
                    total: self.1.total(),
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
        let size = layout.size();
        match self.0.alloc_filled(layout, n) {
            Ok(ptr) => {
                let total = self.1.inc_total_bytes_allocated(size);
                self.1.log(Succ(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: ptr.as_ptr(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Filled(n),
                    total,
                }));
                Ok(ptr)
            }
            Err(e) => {
                self.1.log(Fail(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: null_mut(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Filled(n),
                    total: self.1.total(),
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    fn alloc_patterned<F: Fn(usize) -> u8>(
        &self,
        layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        let size = layout.size();
        match self.0.alloc_patterned(layout, pattern) {
            Ok(ptr) => {
                let total = self.1.inc_total_bytes_allocated(size);
                self.1.log(Succ(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: ptr.as_ptr(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Patterned,
                    total,
                }));
                Ok(ptr)
            }
            Err(e) => {
                self.1.log(Fail(AllocStat::Alloc {
                    region: MemoryRegion {
                        ptr: null_mut(),
                        size,
                        align: layout.align(),
                    },
                    kind: AllocKind::Patterned,
                    total: self.1.total(),
                }));
                Err(e)
            }
        }
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
        let old_size = old_layout.size();
        let new_size = new_layout.size();
        let delta = new_size.saturating_sub(old_size);
        let total = self.1.inc_total_bytes_allocated(delta);
        match self.0.grow(ptr, old_layout, new_layout) {
            Ok(new_ptr) => {
                self.1.log(Succ(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: new_ptr.as_ptr(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Uninitialized,
                    total,
                }));
                Ok(new_ptr)
            }
            Err(e) => {
                // growth failure means its inner allocation failed, NOT its dealloc; thus, there are fewer bytes allocated.
                let total = self.1.dec_total_bytes_allocated(new_size);
                self.1.log(Fail(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: null_mut(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Uninitialized,
                    total,
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();
        let delta = new_size.saturating_sub(old_size);
        let total = self.1.inc_total_bytes_allocated(delta);
        match self.0.grow_zeroed(ptr, old_layout, new_layout) {
            Ok(new_ptr) => {
                self.1.log(Succ(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: new_ptr.as_ptr(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Zeroed,
                    total,
                }));
                Ok(new_ptr)
            }
            Err(e) => {
                let total = self.1.dec_total_bytes_allocated(new_size);
                self.1.log(Fail(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: null_mut(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Zeroed,
                    total,
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    unsafe fn grow_patterned<F: Fn(usize) -> u8>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();
        let delta = new_size.saturating_sub(old_size);
        let total = self.1.inc_total_bytes_allocated(delta);
        match self.0.grow_patterned(ptr, old_layout, new_layout, pattern) {
            Ok(new_ptr) => {
                self.1.log(Succ(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: new_ptr.as_ptr(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Patterned,
                    total,
                }));
                Ok(new_ptr)
            }
            Err(e) => {
                let total = self.1.dec_total_bytes_allocated(new_size);
                self.1.log(Fail(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: null_mut(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Patterned,
                    total,
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    fn grow_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();
        let delta = new_size.saturating_sub(old_size);
        let total = self.1.inc_total_bytes_allocated(delta);
        match self.0.grow_filled(ptr, old_layout, new_layout, n) {
            Ok(new_ptr) => {
                self.1.log(Succ(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: new_ptr.as_ptr(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Filled(n),
                    total,
                }));
                Ok(new_ptr)
            }
            Err(e) => {
                let total = self.1.dec_total_bytes_allocated(new_size);
                self.1.log(Fail(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: null_mut(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Filled(n),
                    total,
                }));
                Err(e)
            }
        }
    }

    #[track_caller]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();
        let delta = old_size.saturating_sub(new_size);
        let total = self.1.dec_total_bytes_allocated(delta);
        match self.0.shrink(ptr, old_layout, new_layout) {
            Ok(new_ptr) => {
                self.1.log(Succ(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: new_ptr.as_ptr(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Shrink,
                    total,
                }));
                Ok(new_ptr)
            }
            Err(e) => {
                self.1.dec_total_bytes_allocated(new_size - delta);
                self.1.log(Fail(AllocStat::Realloc {
                    info: ResizeInfo {
                        old: MemoryRegion {
                            ptr: ptr.as_ptr(),
                            size: old_size,
                            align: old_layout.align(),
                        },
                        new: MemoryRegion {
                            ptr: null_mut(),
                            size: new_size,
                            align: new_layout.align(),
                        },
                    },
                    kind: AllocKind::Shrink,
                    total,
                }));
                Err(e)
            }
        }
    }
}
