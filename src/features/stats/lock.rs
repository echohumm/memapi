use std::io::{Stderr, StderrLock, Stdout, StdoutLock, Write, stderr, stdout};

/// A trait for locking an output stream in a thread-safe manner.
pub trait WriteLock: Send + Sync {
    /// The guard type.
    type Guard: Write;

    /// Locks the output stream and returns a guard to write to it.
    fn lock(&self) -> Self::Guard;
}

macro_rules! impl_ref {
    ($($ty:ident),*) => {
		$(
			impl WriteLock for &$ty {
				type Guard = <$ty as WriteLock>::Guard;

				fn lock(&self) -> Self::Guard {
					(**self).lock()
				}
			}

			impl WriteLock for &mut $ty {
				type Guard = <$ty as WriteLock>::Guard;

				fn lock(&self) -> Self::Guard {
					(**self).lock()
				}
			}
		)*
	};
}

impl WriteLock for Stdout {
    type Guard = StdoutLock<'static>;

    fn lock(&self) -> StdoutLock<'static> { stdout().lock() }
}

impl WriteLock for Stderr {
    type Guard = StderrLock<'static>;

    fn lock(&self) -> StderrLock<'static> { stderr().lock() }
}

impl_ref!(Stdout, Stderr);

impl<W: WriteLock> WriteLock for Box<W> {
    type Guard = W::Guard;

    fn lock(&self) -> Self::Guard { (**self).lock() }
}

#[cfg(not(feature = "no_alloc"))]
impl<W: WriteLock> WriteLock for alloc::sync::Arc<W> {
    type Guard = W::Guard;

    fn lock(&self) -> W::Guard { (**self).lock() }
}
