use alloc::alloc::Layout;
use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    ptr::NonNull,
};

/// Errors for allocation operations.
#[derive(Debug)]
#[repr(u8)]
#[cfg_attr(not(feature = "std"), derive(Clone, Copy))]
#[allow(clippy::module_name_repetitions)]
pub enum AllocError {
    /// The underlying allocator failed to allocate using the given layout; see the contained cause.
    ///
    /// The contained cause may or may not be accurate depending on the environment.
    AllocFailed(Layout, Cause),
    /// The layout computed with the given size and alignment is invalid; see the contained reason.
    InvalidLayout(usize, usize, LayoutErr),
    /// The given layout was zero-sized. The contained [`NonNull`] will be dangling and valid for
    /// the requested alignment.
    ///
    /// This can, in many cases, be considered a success.
    ZeroSizedLayout(NonNull<u8>),
    /// Attempted to grow to a smaller size.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger size.
    ShrinkBiggerNewLayout(usize, usize),
    /// An arithmetic operation would overflow.
    ///
    /// This error contains both sides of the operation and the operation itself.
    ArithmeticOverflow(usize, ArithOp, usize),
    /// Any other kind of error, in the form of a string.
    Other(&'static str),
}

// manual implementations because of Cause, which can't be PEq
impl PartialEq for AllocError {
    #[inline]
    fn eq(&self, other: &AllocError) -> bool {
        use AllocError::{
            AllocFailed, ArithmeticOverflow, GrowSmallerNewLayout, InvalidLayout, Other,
            ShrinkBiggerNewLayout, ZeroSizedLayout,
        };

        match (self, other) {
            #[cfg(not(feature = "os_err_reporting"))]
            (AllocFailed(l1, c1), AllocFailed(l2, c2)) => l1 == l2 && c1 == c2,
            #[cfg(feature = "os_err_reporting")]
            // compiler is stupid and thinks this is unreachable (or i am and it is)
            #[allow(unreachable_patterns)]
            (AllocFailed(l1, _), AllocFailed(l2, _)) => l1 == l2,
            (InvalidLayout(sz1, aln1, _), InvalidLayout(sz2, aln2, _)) => {
                sz1 == sz2 && aln1 == aln2
            }
            (ZeroSizedLayout(a), ZeroSizedLayout(b)) => a == b,
            (GrowSmallerNewLayout(old1, new1), GrowSmallerNewLayout(old2, new2))
            | (ShrinkBiggerNewLayout(old1, new1), ShrinkBiggerNewLayout(old2, new2)) => {
                old1 == old2 && new1 == new2
            }
            (ArithmeticOverflow(lhs1, op1, rhs1), ArithmeticOverflow(lhs2, op2, rhs2)) => {
                lhs1 == lhs2 && op1 == op2 && rhs1 == rhs2
            }
            (Other(a), Other(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for AllocError {}

impl Display for AllocError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            AllocError::AllocFailed(l, cause) => {
                write!(f, "allocation failed for layout:\n\t{:?}\ncause: {}", l, cause)
            }
            AllocError::InvalidLayout(sz, align, reason) => {
                write!(
                    f,
                    "computed invalid layout:\n\tsize: {},\n\talign: {}\nreason: {}",
                    sz, align, reason
                )
            }
            AllocError::ZeroSizedLayout(_) => {
                write!(f, "zero-sized layout was given")
            }
            AllocError::GrowSmallerNewLayout(old, new) => write!(
                f,
                "attempted to grow from a size of {} to a smaller size of {}",
                old, new
            ),
            AllocError::ShrinkBiggerNewLayout(old, new) => write!(
                f,
                "attempted to shrink from a size of {} to a larger size of {}",
                old, new
            ),
            AllocError::ArithmeticOverflow(lhs, op, rhs) => {
                write!(
                    f,
                    "arithmetic operation would overflow: {} {} {}",
                    lhs, op, rhs
                )
            }
            AllocError::Other(other) => write!(f, "{}", other),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AllocError {}

/// An error that can occur when computing a layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LayoutErr {
    /// The alignment is zero.
    ZeroAlign,
    /// The alignment is not a power of two.
    NonPowerOfTwoAlign,
    /// The requested size was greater than
    /// [`USIZE_MAX_NO_HIGH_BIT`](crate::type_props::USIZE_MAX_NO_HIGH_BIT) when rounded up to the
    /// nearest multiple of the requested alignment.
    Overflow,
}

impl Display for LayoutErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LayoutErr::ZeroAlign => write!(f, "alignment is zero"),
            LayoutErr::NonPowerOfTwoAlign => write!(f, "alignment is not a power of two"),
            LayoutErr::Overflow => write!(f, "size would overflow"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for LayoutErr {}

/// An arithmetic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ArithOp {
    /// Addition. (+)
    Add,
    /// Subtraction. (-)
    Sub,
    /// Multiplication. (*)
    Mul,
    /// Division. (/)
    Div,
    /// Modulo. (%)
    Rem,
}

impl Display for ArithOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ArithOp::Add => write!(f, "+"),
            ArithOp::Sub => write!(f, "-"),
            ArithOp::Mul => write!(f, "*"),
            ArithOp::Div => write!(f, "/"),
            ArithOp::Rem => write!(f, "%"),
        }
    }
}

/// The cause of an [`AllocError::AllocFailed`] error.
#[derive(Debug)]
#[cfg_attr(not(feature = "os_err_reporting"), derive(Clone, Copy, PartialEq, Eq))]
#[repr(u8)]
pub enum Cause {
    /// The cause is unknown.
    Unknown,
    #[cfg(feature = "os_err_reporting")]
    /// The cause is described in the contained OS error.
    ///
    /// The error may or may not be accurate depending on the environment.
    OSErr(std::io::Error),
}

impl Display for Cause {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Cause::Unknown => write!(f, "unknown"),
            #[cfg(feature = "os_err_reporting")]
            #[allow(clippy::used_underscore_binding)]
            Cause::OSErr(e) => write!(f, "os error: {}", e),
        }
    }
}