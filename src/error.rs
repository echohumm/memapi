use alloc::alloc::Layout;
use core::{
    error::Error,
    fmt::{self, Display, Formatter},
    ptr::NonNull,
};

/// Errors for allocation operations.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[repr(u8)]
pub enum AllocError {
    /// The layout computed with the given size and alignment is invalid.
    LayoutError(usize, usize),
    /// The given layout was zero-sized. The contained [`NonNull`] will be dangling and valid for
    /// the requested alignment.
    ///
    /// This can, in many cases, be considered a success.
    ZeroSizedLayout(NonNull<u8>),
    /// The underlying allocator failed to allocate using the given layout.
    AllocFailed(Layout),
    /// Attempted to grow to a smaller layout.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger layout.
    ShrinkBiggerNewLayout(usize, usize),
	/// Attempted to reallocate, grow, or shrink to the same size.
	EqualSizeRealloc,
    /// An operation unsupported by the allocator was attempted.
    UnsupportedOperation(&'static str),
    /// Any other kind of error.
    Other(&'static str),
}

impl Display for AllocError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AllocError::LayoutError(sz, align) => {
                write!(f, "computed invalid layout: size: {sz}, align: {align}")
            }
            AllocError::ZeroSizedLayout(_) => {
                write!(f, "zero-sized layout was given")
            }
            AllocError::AllocFailed(l) => write!(f, "allocation failed for layout: {l:?}"),
            AllocError::GrowSmallerNewLayout(old, new) => write!(
                f,
                "attempted to grow from a size of {old} to a smaller size of {new}"
            ),
            AllocError::ShrinkBiggerNewLayout(old, new) => write!(
                f,
                "attempted to shrink from a size of {old} to a larger size of {new}"
            ),
			AllocError::EqualSizeRealloc => write!(f, "attempted to reallocate, grow, or shrink to \
			the same size"),
            AllocError::UnsupportedOperation(op) => {
                write!(f, "unsupported operation: attempted to {op}")
            }
            AllocError::Other(other) => write!(f, "{other}"),
        }
    }
}

impl Error for AllocError {}
