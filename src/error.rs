use {
    crate::{Layout, data::type_props::SizedProps},
    core::{
        fmt::{Debug, Display, Formatter, Result as FmtResult},
        ptr::NonNull
    }
};

/// Errors for allocator operations.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AllocError {
    /// The underlying allocator failed to allocate using the given layout; see the contained cause.
    ///
    /// The cause may or may not be accurate depending on the type and environment.
    AllocFailed(Layout, Cause),
    /// The layout computed with the given size and alignment is invalid; see the contained reason.
    InvalidLayout(InvLayout),
    /// The given alignment was invalid; see the contained information.
    InvalidAlign(AlignErr),
    /// The given layout was zero-sized. The contained [`NonNull`] will be dangling and valid for
    /// the requested alignment.
    ///
    /// This can, in many cases, be considered a success.
    ZeroSizedLayout(NonNull<u8>),
    /// Attempted to grow to a smaller size.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger size.
    ShrinkLargerNewLayout(usize, usize),
    /// An arithmetic error.
    ArithmeticError(ArithErr),
    /// Any other kind of error, in the form of a string.
    Other(&'static str)
}

impl Display for AllocError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use AllocError::{
            AllocFailed,
            ArithmeticError,
            GrowSmallerNewLayout,
            InvalidAlign,
            InvalidLayout,
            Other,
            ShrinkLargerNewLayout,
            ZeroSizedLayout
        };

        match self {
            AllocFailed(l, cause) => write!(
                f,
                "allocation failed:\n\tlayout:\n\t\tsize: {}\n\t\talign: {}\n\tcause: {}",
                l.size(),
                l.align(),
                cause
            ),
            InvalidLayout(inv_layout) => write!(f, "{}", inv_layout),
            InvalidAlign(inv_align) => write!(f, "{}", inv_align),
            ZeroSizedLayout(_) => write!(f, "received a zero-sized layout"),
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

#[cfg(feature = "std")]
impl std::error::Error for AllocError {}

/// The cause of an error.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum Cause {
    /// The cause is unknown.
    ///
    /// This most commonly means an [`OSErr`](Cause::OSErr) occurred, but `os_err_reporting` is
    /// disabled.
    Unknown,
    /// The allocator ran out of memory.
    ///
    /// This should only be used when the __allocator__ runs out of memory and doesn't grow. Use
    /// [`OSErr`](Cause::OSErr) if the system runs out of memory.
    OutOfMemory,
    // TODO: better docs
    /// An error occurred while rounding the alignment of the requested layout up to a value
    /// compatible with [`CAlloc`](crate::c_alloc::alloc::CAlloc).
    CRoundUp,
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
            // TODO: better error message
            Cause::CRoundUp => {
                write!(f, "failed to round layout alignment up to a multiple of {}", usize::SZ)
            }
            #[cfg(feature = "os_err_reporting")]
            Cause::OSErr(e) => write!(f, "os error:\n\t{}", e)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Cause {}

/// An invalid layout and the reason for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvLayout(pub usize, pub usize, pub LayoutErr);

impl Display for InvLayout {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "computed invalid layout:\n\tsize: {},\n\talign: {}\n\treason: {}",
            self.0, self.1, self.2
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvLayout {}

/// An error that can occur when computing a layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LayoutErr {
    /// The alignment was invalid.
    Align(AlignErr),
    /// The requested size was greater than
    /// [`USIZE_MAX_NO_HIGH_BIT`](crate::data::type_props::USIZE_MAX_NO_HIGH_BIT) when
    /// rounded up to the nearest multiple of the requested alignment.
    ExceedsMax,
    /// An arithmetic error occurred.
    ArithErr(ArithErr)
}

impl Display for LayoutErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LayoutErr::Align(inv_align) => write!(f, "{}", inv_align),
            LayoutErr::ExceedsMax => write!(f, "size would overflow when rounded up to alignment"),
            LayoutErr::ArithErr(overflow) => write!(f, "layout err: {}", overflow)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for LayoutErr {}

/// The reason for an invalid alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AlignErr {
    /// The alignment is zero.
    ZeroAlign,
    /// The alignment isn't a power of two.
    NonPowerOfTwoAlign(usize)
}

impl Display for AlignErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            AlignErr::ZeroAlign => write!(f, "alignment is zero"),
            AlignErr::NonPowerOfTwoAlign(align) => {
                write!(f, "alignment {} isn't a power of two", align)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AlignErr {}

/// An arithmetic error.
///
/// Either an overflow containing the lhs, op, and rhs, or a case where the rhs is too large and
/// that rhs value. Divide-by-zero errors are considered overflows.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ArithErr {
    /// The right-hand side of the operation is too large for the operation.
    TooLargeRhs(usize),
    /// An overflow would occur.
    Overflow(usize, ArithOp, usize)
}

impl Display for ArithErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ArithErr::TooLargeRhs(rhs) => {
                write!(f, "right-hand side {} is too large for the operation", rhs)
            }
            ArithErr::Overflow(l, o, r) => {
                write!(f, "arithmetic operation would overflow: {} {} {}", l, o, r)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ArithErr {}

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

/// An error that can occur when creating a layout for repeated instances of a type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(clippy::module_name_repetitions)]
#[repr(u8)]
pub enum RepeatLayoutError {
    /// The computed layout is invalid.
    InvalidLayout(InvLayout),
    /// An error occurred when performing an arithmetic operation.
    ArithmeticError(ArithErr)
}

impl Display for RepeatLayoutError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            RepeatLayoutError::InvalidLayout(inv_layout) => write!(f, "{}", inv_layout),
            RepeatLayoutError::ArithmeticError(err) => write!(f, "{}", err)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RepeatLayoutError {}
