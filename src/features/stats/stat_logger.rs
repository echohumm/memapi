use {
    crate::{error::ArithOp, helpers::checked_op_panic, stats::AllocRes},
    core::sync::atomic::{
        AtomicUsize,
        Ordering::{Acquire, Release}
    }
};

#[cfg(all(feature = "std", not(feature = "stats_parking_lot")))]
type Mutex<T> = std::sync::Mutex<T>;
#[cfg(feature = "stats_parking_lot")]
type Mutex<T> = parking_lot::Mutex<T>;

#[cfg(all(feature = "std", not(feature = "stats_parking_lot")))]
type MutexGuard<'a, T> = std::sync::MutexGuard<'a, T>;
#[cfg(feature = "stats_parking_lot")]
type MutexGuard<'a, T> = parking_lot::MutexGuard<'a, T>;

#[cfg(any(feature = "std", feature = "stats_parking_lot"))]
fn lock_mutex_expect<'a, T>(mutex: &'a Mutex<T>, _msg: &str) -> MutexGuard<'a, T> {
    #[cfg(all(feature = "std", not(feature = "stats_parking_lot")))]
    {
        #[allow(clippy::used_underscore_binding)]
        mutex.lock().expect(_msg)
    }
    #[cfg(feature = "stats_parking_lot")]
    {
        mutex.lock()
    }
}

// noop logger
#[allow(clippy::inline_always)]
impl StatsLogger for () {
    // none of these do anything, so we just inline them.
    #[inline(always)]
    fn log(&self, _: AllocRes) {}

    #[inline(always)]
    fn inc_total_bytes_allocated(&self, _: usize) -> usize { 0 }

    #[inline(always)]
    fn dec_total_bytes_allocated(&self, _: usize) -> usize { 0 }

    #[inline(always)]
    fn total(&self) -> usize { 0 }
}

/// Internal helper of [`atomic_total_ops`] for adding to an atomic value.
#[doc(hidden)]
pub fn inc_atomic(atomic: &AtomicUsize, bytes: usize) -> usize {
    let res = checked_op_panic(atomic.load(Acquire), ArithOp::Add, bytes);
    atomic.store(res, Release);
    res
}

/// Internal helper of [`atomic_total_ops`] for subtracting from an atomic value.
#[doc(hidden)]
pub fn dec_atomic(atomic: &AtomicUsize, bytes: usize) -> usize {
    let res = checked_op_panic(atomic.load(Acquire), ArithOp::Sub, bytes);
    atomic.store(res, Release);
    res
}

#[macro_export]
/// Helper macro to implement the default atomic total operations for a `StatsLogger`.
macro_rules! atomic_total_ops {
    ($($field:ident)?) => {
            #[inline(always)]
            fn inc_total_bytes_allocated(&self, bytes: usize) -> usize {
                $crate::stats::inc_atomic(&self$(.$field)?, bytes)
            }

            #[inline(always)]
            fn dec_total_bytes_allocated(&self, bytes: usize) -> usize {
                $crate::stats::dec_atomic(&self$(.$field)?, bytes)
            }

            #[inline(always)]
            fn total(&self) -> usize {
                self$(.$field)?.load(Acquire)
            }
    };
}

// byte counter-only logger (no stat)
impl StatsLogger for AtomicUsize {
    atomic_total_ops!();

    #[inline(always)]
    fn log(&self, _: AllocRes) {}
}

/// Delegate all calls to the inner logger.
macro_rules! delegate_logger {
    ($ty:ty) => {
        impl<L: StatsLogger + ?Sized> StatsLogger for $ty {
            #[inline(always)]
            fn log(&self, stat: AllocRes) { (**self).log(stat) }

            #[inline(always)]
            fn inc_total_bytes_allocated(&self, bytes: usize) -> usize {
                (**self).inc_total_bytes_allocated(bytes)
            }

            #[inline(always)]
            fn dec_total_bytes_allocated(&self, bytes: usize) -> usize {
                (**self).dec_total_bytes_allocated(bytes)
            }

            #[inline(always)]
            fn total(&self) -> usize { (**self).total() }
        }
    };
}

delegate_logger!(&L);
delegate_logger!(&mut L);
#[cfg(not(feature = "no_alloc"))]
delegate_logger!(alloc::boxed::Box<L>);
#[cfg(not(feature = "no_alloc"))]
delegate_logger!(alloc::rc::Rc<L>);
#[cfg(not(feature = "no_alloc"))]
delegate_logger!(alloc::sync::Arc<L>);

#[cfg(feature = "std")]
/// An IO buffer that can be used to log statistics.
pub struct IOLog<W: std::io::Write> {
    /// The writer to log to.
    pub buf: Mutex<W>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize
}

#[cfg(any(feature = "std", feature = "stats_parking_lot"))]
/// A buffer that can be used to log statistics.
pub struct FmtLog<W: core::fmt::Write> {
    /// The writer to log to.
    pub buf: Mutex<W>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize
}

#[cfg(all(any(feature = "std", feature = "stats_parking_lot"), not(feature = "no_alloc")))]
/// A logger that pushes all statistics to a vector.
pub struct StatCollectingLog {
    /// The vector which results are passed to.
    pub results: Mutex<alloc::vec::Vec<AllocRes>>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize
}

#[cfg(feature = "stats_thread_safe_io")]
/// A thread-safe logger that writes to a lockable, writable type.
pub struct ThreadSafeIOLog<W: super::lock::WriteLock> {
    buf: W,
    total: AtomicUsize
}

#[cfg(feature = "std")]
impl<W: std::io::Write> StatsLogger for IOLog<W> {
    atomic_total_ops!(total);

    fn log(&self, stat: AllocRes) {
        lock_mutex_expect(&self.buf, "inner `Mutex<W>` for `WrittenLog` was poisoned")
            .write_all(format!("{}\n", stat).as_bytes())
            .expect("failed to write to inner `W` of `WrittenLog`");
    }
}

#[cfg(any(feature = "std", feature = "stats_parking_lot"))]
impl<W: core::fmt::Write> StatsLogger for FmtLog<W> {
    atomic_total_ops!(total);

    fn log(&self, stat: AllocRes) {
        lock_mutex_expect(&self.buf, "inner `Mutex<W>` for `FmtLog` was poisoned")
            .write_fmt(format_args!("{}\n", stat))
            .expect("failed to write to inner `W` of `FmtLog`");
    }
}

#[cfg(all(any(feature = "std", feature = "stats_parking_lot"), not(feature = "no_alloc")))]
impl StatsLogger for StatCollectingLog {
    atomic_total_ops!(total);

    fn log(&self, stat: AllocRes) {
        lock_mutex_expect(
            &self.results,
            "inner `Mutex<Vec<AllocRes>>` for `StatCollectingLog` was poisoned"
        )
        .push(stat);
    }
}

#[cfg(feature = "stats_thread_safe_io")]
impl<W: super::lock::WriteLock> StatsLogger for ThreadSafeIOLog<W> {
    atomic_total_ops!(total);

    fn log(&self, stat: AllocRes) {
        <W::Guard as std::io::Write>::write_all(
            &mut self.buf.lock(),
            format!("{}\n", stat).as_bytes()
        )
        .expect("failed to write to inner `W` of `WrittenLog`");
    }
}

#[cfg(feature = "std")]
impl Default for IOLog<std::io::Stdout> {
    fn default() -> IOLog<std::io::Stdout> {
        IOLog { buf: Mutex::new(std::io::stdout()), total: AtomicUsize::new(0) }
    }
}

#[cfg(feature = "std")]
impl Default for IOLog<std::fs::File> {
    fn default() -> IOLog<std::fs::File> {
        IOLog {
            buf: Mutex::new(std::fs::File::create("alloc_stats.log").unwrap()),
            total: AtomicUsize::new(0)
        }
    }
}

#[cfg(feature = "std")]
impl<W: core::fmt::Write + Default> Default for FmtLog<W> {
    fn default() -> FmtLog<W> {
        FmtLog { buf: Mutex::new(W::default()), total: AtomicUsize::new(0) }
    }
}

#[cfg(all(any(feature = "std", feature = "stats_parking_lot"), not(feature = "no_alloc")))]
impl Default for StatCollectingLog {
    fn default() -> StatCollectingLog {
        StatCollectingLog {
            results: Mutex::new(alloc::vec::Vec::new()),
            total: AtomicUsize::new(0)
        }
    }
}

#[cfg(feature = "stats_thread_safe_io")]
impl<W: super::lock::WriteLock + Default> Default for ThreadSafeIOLog<W> {
    fn default() -> ThreadSafeIOLog<W> { ThreadSafeIOLog::new(W::default()) }
}

#[cfg(feature = "std")]
impl<W: std::io::Write> From<W> for IOLog<W> {
    fn from(w: W) -> IOLog<W> { IOLog::new(w) }
}

#[cfg(feature = "std")]
impl<W: core::fmt::Write> From<W> for FmtLog<W> {
    fn from(w: W) -> FmtLog<W> { FmtLog::new(w) }
}

#[cfg(feature = "stats_thread_safe_io")]
impl<W: super::lock::WriteLock> From<W> for ThreadSafeIOLog<W> {
    fn from(value: W) -> ThreadSafeIOLog<W> { ThreadSafeIOLog::new(value) }
}

#[cfg(feature = "std")]
impl<W: std::io::Write> IOLog<W> {
    const_if! {
        "const_extras",
        "Creates a new [`IOLog`] from a writer.",
        #[inline]
        pub const fn new(buf: W) -> IOLog<W> {
            IOLog {
                buf: Mutex::new(buf),
                total: AtomicUsize::new(0),
            }
        }
    }
}

#[cfg(feature = "std")]
impl<W: core::fmt::Write> FmtLog<W> {
    const_if! {
        "const_extras",
        "Creates a new [`FmtLog`] from a writer.",
        #[inline]
        pub const fn new(buf: W) -> FmtLog<W> {
            FmtLog {
                buf: Mutex::new(buf),
                total: AtomicUsize::new(0),
            }
        }
    }

    /// Gets a reference to the log.
    ///
    /// # Panics
    ///
    /// This function will panic if the inner [`Mutex`](std::sync::Mutex) is poisoned.
    pub fn get_log(&self) -> MutexGuard<'_, W> {
        lock_mutex_expect(&self.buf, "inner `Mutex<W>` for `FmtLog` was poisoned")
    }
}

#[cfg(feature = "stats_thread_safe_io")]
impl<W: super::lock::WriteLock> ThreadSafeIOLog<W> {
    const_if! {
        "const_extras",
        "Creates a new [`ThreadSafeIOLog`] from a lockable, writable type.",
        #[inline]
        pub const fn new(buf: W) -> ThreadSafeIOLog<W> {
            ThreadSafeIOLog {
                buf,
                total: AtomicUsize::new(0),
            }
        }
    }
}

// TODO: make sure all cfgs are right because some (like below) were wrong (was just feature= "std")

#[cfg(all(any(feature = "std", feature = "stats_parking_lot"), not(feature = "no_alloc")))]
impl StatCollectingLog {
    const_if! {
        "const_extras",
        "Creates a new [`StatCollectingLog`].",
        #[must_use]
        #[inline]
        pub const fn new() -> StatCollectingLog {
            StatCollectingLog {
                results: Mutex::new(alloc::vec::Vec::new()),
                total: AtomicUsize::new(0),
            }
        }
    }

    /// Creates a new [`StatCollectingLog`] with the given capacity.
    #[must_use]
    #[inline]
    pub fn with_capacity(cap: usize) -> StatCollectingLog {
        StatCollectingLog {
            results: Mutex::new(alloc::vec::Vec::with_capacity(cap)),
            total: AtomicUsize::new(0)
        }
    }
}

#[cfg(feature = "stats_file_lock")]
/// A logger that writes to a file.
pub struct FileLog {
    /// The file to log to.
    pub file: Mutex<std::fs::File>,
    /// The total number of bytes allocated.
    pub total: AtomicUsize
}

#[cfg(feature = "stats_file_lock")]
impl FileLog {
    /// Creates a new [`FileLog`] with the given options and path.
    ///
    /// # Errors
    ///
    /// Returns an error if opening the file fails.
    ///
    /// See [`OpenOptions::open`](std::fs::OpenOptions::open) for the specific errors.
    ///
    /// # Note
    ///
    /// This may cause a panic when attempting to log later if the file is not writable.
    #[inline]
    pub fn new<P: AsRef<std::path::Path>>(
        opt: &std::fs::OpenOptions,
        path: P
    ) -> Result<Self, std::io::Error> {
        Ok(FileLog { file: Mutex::new(tri!(do opt.open(path))), total: AtomicUsize::new(0) })
    }
}

#[cfg(feature = "stats_file_lock")]
impl StatsLogger for FileLog {
    atomic_total_ops!(total);

    fn log(&self, stat: AllocRes) {
        use std::io::Write;

        let mut guard =
            lock_mutex_expect(&self.file, "inner `Mutex<File>` for `FileLog` was poisoned");

        #[allow(unknown_lints, clippy::incompatible_msrv)]
        guard.lock().expect("failed to lock `File`");
        #[allow(unknown_lints, clippy::incompatible_msrv)]
        guard
            .write_all(format!("{}\n", stat).as_bytes())
            .expect("failed to write to inner `File` of `FileLog`");
        #[allow(unknown_lints, clippy::incompatible_msrv)]
        guard.unlock().expect("failed to unlock `File`");
    }
}

#[cfg(all(not(feature = "stats_file_lock"), feature = "std"))]
/// A logger that writes to a file.
pub type FileLog = IOLog<std::fs::File>;

#[cfg(feature = "stats_thread_safe_io")]
/// A logger that writes to stdout.
pub type StdoutLog = ThreadSafeIOLog<std::io::Stdout>;

#[cfg(feature = "stats_thread_safe_io")]
/// A logger that writes to stderr.
pub type StderrLog = ThreadSafeIOLog<std::io::Stderr>;

#[cfg(all(not(feature = "stats_thread_safe_io"), feature = "std"))]
/// A logger that writes to stdout.
pub type StdoutLog = IOLog<std::io::Stdout>;

#[cfg(all(not(feature = "stats_thread_safe_io"), feature = "std"))]
/// A logger that writes to stderr.
pub type StderrLog = IOLog<std::io::Stderr>;

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
/// ```rust
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
///
/// # Panics
///
/// All methods in this trait may panic if the inner synchronization primitive is poisoned.
#[allow(clippy::module_name_repetitions)]
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
