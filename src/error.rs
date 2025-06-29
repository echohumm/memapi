use alloc::alloc::Layout;
use core::{
    error::Error,
    fmt::{self, Display, Formatter},
    ptr::NonNull,
};

/// Errors for allocation operations.
///
/// # Type parameters
///
/// - `O`: The type which the `Other` variant wraps.
/// - `UO`: The type which `UnsupportedOperation::`[`UOp::Other`] wraps.
#[derive(Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AllocError<O: Error = Err, UO: Error = Err> {
    /// A basic arithmetic operation overflowed.
    ArithmeticOverflow,
    /// The layout computed with the given size and alignment is invalid.
    LayoutError(usize, usize),
    /// There is not enough memory available for allocation.
    OutOfMemory,
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
    /// An operation unsupported by the allocator was attempted.
    UnsupportedOperation(UOp<UO>),
    #[cfg(feature = "resize_in_place")]
    /// Resize-in-place was found to be impossible.
    // Note that this variant means the allocator supports resizing in-place, but it failed.
    CannotResizeInPlace,
    #[cfg(feature = "resize_in_place")]
    /// A size of zero was requested for a resize-in-place operation.
    ///
    /// Same as [`AllocError::ZeroSizedLayout`], but without the [`NonNull`], which is useless for
    /// in-place operations.
    ResizeInPlaceZeroSized,
    /// Any other kind of error.
    Other(O),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
/// A zero-sized struct, which exists only to be a default type for [`AllocError::Other`] and
/// [`UOp::Other`].
pub struct Err;

impl Display for Err {
    fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl Error for Err {}

#[derive(Debug, PartialEq, Eq)]
#[repr(u8)]
/// An unsupported operation.
pub enum UOp<O: Error = Err> {
    /// A shrink-in-place operation.
    ShrinkInPlace,
    /// A reallocation operation with a different alignment from the original allocation.
    ReallocDiffAlign(usize, usize),
    /// Any other unsupported operation.
    Other(O),
}

impl<O: Error> Display for AllocError<O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AllocError::ArithmeticOverflow => write!(f, "arithmetic overflow"),
            AllocError::LayoutError(sz, align) => {
                write!(f, "computed invalid layout: size: {sz}, align: {align}")
            }
            AllocError::OutOfMemory => write!(f, "out of memory"),
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
            AllocError::UnsupportedOperation(op) => {
                write!(f, "unsupported operation: attempted to {op}")
            }
            #[cfg(feature = "resize_in_place")]
            AllocError::CannotResizeInPlace => write!(f, "cannot resize in place"),
            #[cfg(feature = "resize_in_place")]
            AllocError::ResizeInPlaceZeroSized => {
                write!(f, "zero-sized resize in place was requested")
            }
            AllocError::Other(other) => write!(f, "allocation error: {other}"),
        }
    }
}

impl<O: Error> Display for UOp<O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            UOp::ShrinkInPlace => write!(f, "shrink in place"),
            UOp::ReallocDiffAlign(old, new) => {
                write!(f, "realloc diff align from {old} to {new}")
            }
            UOp::Other(other) => write!(f, "{other}"),
        }
    }
}

impl Error for AllocError {}
