use core::ffi::CStr;
#[cfg(feature = "metadata")]
use core::ptr::Pointee;
#[cfg(feature = "std")]
use std::{
	path::Path,
	ffi::OsStr,
};

/// Unsafe marker trait for types that can be copied, including unsized types such as slices.
///
/// # Safety
///
/// Implementing `UnsizedCopy` indicates the type's memory representation can be duplicated without
/// violating soundness or causing double frees.
pub unsafe trait UnsizedCopy {}

// Any `T` which is `Copy` is also `UnsizedCopy`.
unsafe impl<T: Copy> UnsizedCopy for T {}
// And so are slices containing copyable T.    ↰
unsafe impl<T: Copy> UnsizedCopy for [T] {} // |
// `str == [u8]` and `u8: Copy`.               ┤
unsafe impl UnsizedCopy for str {} //          |
// `CStr == [u8]` and `u8: Copy`               ┤
unsafe impl UnsizedCopy for CStr {} //         |
#[cfg(feature = "std")]
// `OsStr == [u8]` and `u8: Copy`              ┤
unsafe impl UnsizedCopy for OsStr {} //        |
#[cfg(feature = "std")]
// `Path == OsStr == [u8]` and `u8: Copy`.     ┘
unsafe impl UnsizedCopy for Path {}

/// Trait indicating that a type has no metadata.
///
/// This usually means `Self: Sized` or `Self` is `extern`.
///
/// # Example
///
/// ```rust
/// # use memapi::{SizedProps, Thin};
///
/// fn safe<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
#[cfg(feature = "metadata")]
pub trait Thin: Pointee<Metadata = ()> {}
