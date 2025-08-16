use crate::Layout;
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
    /// The cause may or may not be accurate depending on the type and environment.
    AllocFailed(Layout, Cause),
    #[cfg(feature = "fallible_dealloc")]
    /// The underlying allocator failed to deallocate the given pointer using the given layout; see
    /// the contained cause.
    DeallocFailed(NonNull<u8>, Layout, Cause),
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
    ShrinkBiggerNewLayout(usize, usize),
    /// An arithmetic operation would overflow.
    ///
    /// This error contains both sides of the operation and the operation itself.
    ArithmeticOverflow(ArithOverflow),
    /// Any other kind of error, in the form of a string.
    Other(&'static str),
}

impl AllocError {
    #[cfg(feature = "fallible_dealloc")]
    #[cold]
    #[inline(never)]
    #[cfg_attr(not(feature = "dev"), doc(hidden))]
    pub const fn dealloc_failed(
        p: NonNull<u8>,
        layout: Layout,
        block_stat: crate::BlockStatus,
    ) -> Result<(), AllocError> {
        Err(AllocError::DeallocFailed(
            p,
            layout,
            Cause::InvalidBlockStatus(block_stat),
        ))
    }

    #[cold]
    #[inline(never)]
    #[cfg_attr(not(feature = "dev"), doc(hidden))]
    pub const fn arith_overflow(l: usize, op: ArithOp, r: usize) -> Result<usize, ArithOverflow> {
        Err(ArithOverflow(l, op, r))
    }

    // TODO: similar cold constructors for other errors
}

// manual implementations because of Cause, which can't be PEq if os_err_reporting is enabled
impl PartialEq for AllocError {
    #[inline]
    fn eq(&self, other: &AllocError) -> bool {
        use AllocError::{
            AllocFailed, ArithmeticOverflow, GrowSmallerNewLayout, InvalidLayout, Other,
            ShrinkBiggerNewLayout, ZeroSizedLayout,
        };

        match (self, other) {
            (AllocFailed(l1, c1), AllocFailed(l2, c2)) => l1 == l2 && c1 == c2,
            #[cfg(feature = "fallible_dealloc")]
            (AllocError::DeallocFailed(p1, l1, c1), AllocError::DeallocFailed(p2, l2, c2)) => {
                p1 == p2 && l1 == l2 && c1 == c2
            }
            (InvalidLayout(il1), InvalidLayout(il2)) => il1 == il2,
            (ZeroSizedLayout(a), ZeroSizedLayout(b)) => a == b,
            (GrowSmallerNewLayout(old1, new1), GrowSmallerNewLayout(old2, new2))
            | (ShrinkBiggerNewLayout(old1, new1), ShrinkBiggerNewLayout(old2, new2)) => {
                old1 == old2 && new1 == new2
            }
            (ArithmeticOverflow(e1), ArithmeticOverflow(e2)) => e1 == e2,
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
                write!(
                    f,
                    "allocation failed:\n\tlayout:\n\t\tsize: {}\n\t\talign: {}\n\tcause: {}",
                    l.size(),
                    l.align(),
                    cause
                )
            }
            #[cfg(feature = "fallible_dealloc")]
            AllocError::DeallocFailed(ptr, l, cause) => {
                use crate::BlockStatus;

                // i hate this
                match cause {
                    Cause::InvalidBlockStatus(BlockStatus::OwnedIncomplete(Some(l))) => {
                        write!(
                            f,
                            "deallocation failed:\n\tptr: {:p}\n\tlayout:\n\t\tsize: {}\n\t\t\
                        align: {}\n\tcause: ",
                            *ptr,
                            l.size(),
                            l.align()
                        )?;
                        write!(
                            f,
                            "owned (incomplete): full layout:\n\t\t\tsize: {}\n\t\t\talign: {}",
                            l.size(),
                            l.align()
                        )
                    }
                    _ => write!(
                        f,
                        "deallocation failed:\n\tptr: {:p}\n\tlayout:\n\t\tsize: {}\n\t\
                    \talign: {}\n\tcause: {}",
                        *ptr,
                        l.size(),
                        l.align(),
                        cause
                    ),
                }
            }
            AllocError::InvalidLayout(inv_layout) => {
                write!(f, "{}", inv_layout)
            }
            AllocError::InvalidAlign(inv_align) => {
                write!(f, "{}", inv_align)
            }
            AllocError::ZeroSizedLayout(_) => {
                write!(f, "received a zero-sized layout")
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
            AllocError::ArithmeticOverflow(overflow) => {
                write!(f, "{}", overflow)
            }
            AllocError::Other(other) => write!(f, "{}", other),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AllocError {}

/// The cause of an error.
#[derive(Debug)]
#[cfg_attr(not(feature = "os_err_reporting"), derive(Clone, Copy, PartialEq, Eq))]
#[repr(u8)]
pub enum Cause {
    /// The cause is unknown.
    Unknown,
    /// The allocator ran out of memory.
    ///
    /// This should only be used when the __allocator__ runs out of memory and doesn't grow. Use
    /// [`OSErr`](Cause::OSErr) if the system runs out of memory.
    OutOfMemory,
    #[cfg(feature = "fallible_dealloc")]
    /// The block status is invalid.
    InvalidBlockStatus(crate::BlockStatus),
    #[cfg(feature = "os_err_reporting")]
    /// The cause is described in the contained OS error.
    ///
    /// The error may or may not be accurate depending on the environment.
    OSErr(std::io::Error),
}

#[cfg(feature = "os_err_reporting")]
impl PartialEq for Cause {
    fn eq(&self, other: &Cause) -> bool {
        match (self, other) {
            (Cause::Unknown, Cause::Unknown) | (Cause::OutOfMemory, Cause::OutOfMemory) => true,
            #[cfg(feature = "fallible_dealloc")]
            (Cause::InvalidBlockStatus(s1), Cause::InvalidBlockStatus(s2)) => s1 == s2,
            (Cause::OSErr(e1), Cause::OSErr(e2)) => e1.kind() == e2.kind(),
            _ => false,
        }
    }
}

impl Display for Cause {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Cause::Unknown => write!(f, "unknown"),
            Cause::OutOfMemory => write!(f, "out of memory"),
            #[cfg(feature = "fallible_dealloc")]
            Cause::InvalidBlockStatus(s) => write!(f, "invalid block status: {}", s),
            #[cfg(feature = "os_err_reporting")]
            Cause::OSErr(e) => write!(f, "os error:\n\t{}", e),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Cause {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// An error that can occur when creating a layout for repeated instances of a type.
#[allow(clippy::module_name_repetitions)]
pub enum RepeatLayoutError {
    /// The computed layout is invalid.
    InvalidLayout(InvLayout),
    /// An arithmetic operation would overflow.
    ArithmeticOverflow(ArithOverflow),
}

impl RepeatLayoutError {
    /// Converts this error into an [`AllocError`].
    #[must_use]
    pub const fn into_alloc_err(self) -> AllocError {
        match self {
            RepeatLayoutError::InvalidLayout(inv_layout) => AllocError::InvalidLayout(inv_layout),
            RepeatLayoutError::ArithmeticOverflow(overflow) => {
                AllocError::ArithmeticOverflow(overflow)
            }
        }
    }
}

impl Display for RepeatLayoutError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            RepeatLayoutError::InvalidLayout(inv_layout) => {
                write!(f, "{}", inv_layout)
            }
            RepeatLayoutError::ArithmeticOverflow(overflow) => {
                write!(f, "{}", overflow)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RepeatLayoutError {}

/// An invalid layout and the reason for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvLayout(pub usize, pub usize, pub LayoutErr);

impl InvLayout {
    /// Converts this error into an [`AllocError`].
    #[must_use]
    pub const fn into_alloc_err(self) -> AllocError {
        AllocError::InvalidLayout(self)
    }
}

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
    /// [`USIZE_MAX_NO_HIGH_BIT`](crate::type_props::USIZE_MAX_NO_HIGH_BIT) when rounded up to the
    /// nearest multiple of the requested alignment.
    Overflow,
}

impl Display for LayoutErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LayoutErr::Align(inv_align) => write!(f, "{}", inv_align),
            LayoutErr::Overflow => write!(f, "size would overflow"),
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
    /// The alignment is not a power of two.
    NonPowerOfTwoAlign(usize),
}

impl Display for AlignErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            AlignErr::ZeroAlign => write!(f, "alignment is zero"),
            AlignErr::NonPowerOfTwoAlign(align) => {
                write!(f, "alignment {} is not a power of two", align)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AlignErr {}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
/// An arithmetic operation that would overflow.
///
/// Contains both sides of the operation and the operation itself.
pub struct ArithOverflow(pub usize, pub ArithOp, pub usize);

impl ArithOverflow {
    /// Converts this error into an [`AllocError`].
    #[must_use]
    pub const fn into_alloc_err(self) -> AllocError {
        AllocError::ArithmeticOverflow(self)
    }
}

impl Display for ArithOverflow {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "arithmetic operation would overflow: {} {} {}",
            self.0, self.1, self.2
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ArithOverflow {}

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
