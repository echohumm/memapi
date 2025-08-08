use alloc::alloc::Layout;
use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    ptr::NonNull,
};

/// Errors for allocation operations.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
#[allow(clippy::module_name_repetitions)]
pub enum AllocError {
    /// The underlying allocator failed to allocate using the given layout.
    AllocFailed(Layout),
    // commented out until implemented
    // /// The underlying allocator failed to allocate using the given layout, with extra context.
    // AllocFailedWithContext(Layout, Context),
    /// The layout computed with the given size and alignment is invalid.
    InvalidLayout(usize, usize),
    /// The given layout was zero-sized. The contained [`NonNull`] will be dangling and valid for
    /// the requested alignment.
    ///
    /// This can, in many cases, be considered a success.
    ZeroSizedLayout(NonNull<u8>),
    /// Attempted to grow to a smaller layout.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger layout.
    ShrinkBiggerNewLayout(usize, usize),
    /// An arithmetic operation would overflow.
    ///
    /// This error contains both sides of the operation and the operation itself.
    ArithmeticOverflow(usize, ArithOp, usize),
    /// Any other kind of error, in the form of a string.
    Other(&'static str),
}

// manual implementations because of the `OtherErr` variant, which can't be PEq, Eq, or Hash
impl PartialEq for AllocError {
    #[inline]
    fn eq(&self, other: &AllocError) -> bool {
        use AllocError::{
            AllocFailed, ArithmeticOverflow, GrowSmallerNewLayout, InvalidLayout, Other,
            ShrinkBiggerNewLayout, ZeroSizedLayout,
        };

        match (self, other) {
            (AllocFailed(l1), AllocFailed(l2)) => l1 == l2,
            // (
            //     AllocError::AllocFailedWithContext(l1, c1),
            //     AllocError::AllocFailedWithContext(l2, c2),
            // ) => l1 == l2 && c1 == c2,
            (InvalidLayout(sz1, aln1), InvalidLayout(sz2, aln2)) => sz1 == sz2 && aln1 == aln2,
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
            AllocError::AllocFailed(l) => write!(f, "allocation failed for layout: {:?}", l),
            // AllocError::AllocFailedWithContext(l, c) => {
            //     write!(f, "allocation failed for layout: {:?}, {}", l, c)
            // }
            AllocError::InvalidLayout(sz, align) => {
                write!(f, "computed invalid layout: size: {}, align: {}", sz, align)
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

/// An arithmetic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// /// Context for an [`AllocError::AllocFailedWithContext`] error.
// pub enum Context {
//     /// The reason for the error.
//     Reason(ErrorCause),
// }
//
// impl Display for Context {
//     fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
//         match self {
//             Context::Reason(cause) => write!(f, "reason: {}", cause),
//         }
//     }
// }
//
// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// /// The cause of an [`AllocError::AllocFailedWithContext`] error.
// pub enum ErrorCause {
//     /// The error was caused by running out of memory.
//     OOM,
// }
//
// impl Display for ErrorCause {
//     fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
//         match self {
//             ErrorCause::OOM => write!(f, "out of memory"),
//         }
//     }
// }
