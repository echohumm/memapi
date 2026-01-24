use {
    crate::{Layout, data::type_props::SizedProps},
    core::fmt::{Debug, Display, Formatter, Result as FmtResult}
};

/// Helper macro to implement the Error trait based on its availability. Uses [`std::error::Error`]
/// if available, or [`core::error::Error`] if not and on a Rust version which supports it.
macro_rules! impl_error {
    ($ty:ident) => {
        #[cfg(feature = "std")]
        impl std::error::Error for $ty {}
        #[cfg(not(feature = "std"))]
        // error_in_core stable since 1.81
        #[rustversion::since(1.81)]
        impl core::error::Error for $ty {}
    };
}

/// Errors for allocator operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Error {
    /// The underlying allocator failed to allocate using the given layout; see the contained cause.
    ///
    /// The cause may or may not be accurate depending on the type and environment.
    AllocFailed(Layout, Cause),
    /// The layout computed with the given size and alignment is invalid; see the contained reason.
    InvalidLayout(usize, usize, LayoutErr),
    /// Attempted to grow to a smaller size.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger size.
    ShrinkLargerNewLayout(usize, usize),
    /// An arithmetic error.
    ArithmeticError(ArithErr),
    /// Any other kind of error, in the form of a string.
    Other(&'static str)
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Error::{
            AllocFailed,
            ArithmeticError,
            GrowSmallerNewLayout,
            InvalidLayout,
            Other,
            ShrinkLargerNewLayout,
        };

        match self {
            AllocFailed(l, cause) => write!(
                f,
                "allocation failed:\n\tlayout:\n\t\tsize: {}\n\t\talign: {}\n\tcause: {}",
                l.size(),
                l.align(),
                cause
            ),
            InvalidLayout(sz, aln, e) => write!(
                f,
                "computed invalid layout:\n\tsize: {},\n\talign: {}\n\treason: {}",
                sz, aln, e
            ),
            GrowSmallerNewLayout(old, new) => {
                write!(f, "attempted to grow from a size of {} to a smaller size of {}", old, new)
            }
            ShrinkLargerNewLayout(old, new) => {
                write!(f, "attempted to shrink from a size of {} to a larger size of {}", old, new)
            }
            ArithmeticError(overflow) => write!(f, "{}", overflow),
            Other(other) => write!(f, "{}", other)
        }
    }
}

impl_error! { Error }

/// The cause of an error.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum Cause {
    /// The cause is unknown.
    ///
    /// This most commonly means an [`OSErr`](Cause::OSErr) occurred, but `os_err_reporting` is
    /// disabled or the allocator does not support OS error reporting.
    Unknown,
    /// The allocator ran out of memory.
    ///
    /// This should only be used when the __allocator__ runs out of memory and doesn't grow. Use
    /// [`OSErr`](Cause::OSErr) if the system runs out of memory.
    OutOfMemory,
    /// Any other cause, in the form of a string.
    Other(&'static str),
    #[cfg(feature = "os_err_reporting")]
    /// The cause is described in the contained OS error.
    ///
    /// The error may or may not be accurate depending on the environment.
    OSErr(i32)
}

impl Display for Cause {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Cause::Unknown => write!(f, "unknown"),
            Cause::OutOfMemory => write!(f, "out of memory"),
            Cause::Other(other) => write!(f, "{}", other),
            #[cfg(feature = "os_err_reporting")]
            Cause::OSErr(e) => write!(f, "os error:\n\t{}", std::io::Error::from_raw_os_error(*e))
        }
    }
}

impl_error! { Cause }

/// An error that can occur when computing a layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LayoutErr {
    /// The alignment was zero.
    ZeroAlign,
    /// The alignment was not a power of two.
    NonPowerOfTwoAlign,
    /// The requested size was greater than
    /// [`USIZE_MAX_NO_HIGH_BIT`](crate::helpers::USIZE_MAX_NO_HIGH_BIT) when
    /// rounded up to the nearest multiple of the requested alignment.
    ExceedsMax,
    /// An arithmetic error occurred.
    ArithErr(ArithErr),
    /// An error occurred while rounding the alignment of the requested layout up to a value
    /// compatible with C's `aligned_alloc`.
    CRoundUp
}

impl Display for LayoutErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LayoutErr::ZeroAlign => write!(f, "alignment is zero"),
            LayoutErr::NonPowerOfTwoAlign => {
                write!(f, "alignment isn't a power of two")
            }
            LayoutErr::ExceedsMax => write!(f, "size would overflow when rounded up to alignment"),
            LayoutErr::ArithErr(overflow) => write!(f, "layout err: {}", overflow),
            LayoutErr::CRoundUp => {
                write!(f, "failed to round layout alignment up to a multiple of {}", usize::SZ)
            }
        }
    }
}

impl_error! { LayoutErr }

/// An arithmetic operation which would cause an "overflow."
///
/// Divide-by-zero errors and exponentiation to powers larger than [`u32::MAX`] are considered
/// overflows.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ArithErr(pub usize, pub ArithOp, pub usize);

impl Display for ArithErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "arithmetic operation would overflow: {} {} {}", self.0, self.1, self.2)
    }
}

impl_error! { ArithErr }

/// An arithmetic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// Exponentiation. (**)
    Pow
}

impl Display for ArithOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ArithOp::Add => write!(f, "+"),
            ArithOp::Sub => write!(f, "-"),
            ArithOp::Mul => write!(f, "*"),
            ArithOp::Div => write!(f, "/"),
            ArithOp::Rem => write!(f, "%"),
            ArithOp::Pow => write!(f, "**")
        }
    }
}
