/// Unsafe marker trait for types that can be copied, including unsized types such as slices.
///
/// # Safety
///
/// Implementing `UnsizedCopy` indicates the type's memory representation can be duplicated without
/// violating soundness or causing double frees.
pub unsafe trait UnsizedCopy {}

// Any `T` which is `Copy` is also `UnsizedCopy`.
unsafe impl<T: Copy> UnsizedCopy for T {}
// And so are slices containing copyable T.
unsafe impl<T: Copy> UnsizedCopy for [T] {}
// `str == [u8]` and `u8: Copy`.
unsafe impl UnsizedCopy for str {}
#[cfg(feature = "c_str")]
// `CStr == [u8]` and `u8: Copy`
unsafe impl UnsizedCopy for core::ffi::CStr {}
#[cfg(feature = "std")]
// `OsStr == [u8]` and `[u8]: UnsizedCopy`
unsafe impl UnsizedCopy for std::ffi::OsStr {}
#[cfg(feature = "std")]
// `Path == OsStr` and `OsStr: UnsizedCopy`.
unsafe impl UnsizedCopy for std::path::Path {}

#[cfg(all(feature = "metadata", not(feature = "sized_hierarchy")))]
/// Trait indicating that a type has no metadata.
///
/// This usually means `Self: Sized` or `Self` is `extern`.
///
/// # Example
///
// invalid block type here suppresses an (incorrect) error in my ide
/// ```rs
/// # use memapi::type_props::{SizedProps, Thin};
///
/// fn safe<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub trait Thin: core::ptr::Pointee<Metadata = ()> {}
#[cfg(all(feature = "metadata", feature = "sized_hierarchy"))]
/// Trait indicating that a type has no metadata and may or may not have a size.
///
/// # Example
///
// invalid block type here suppresses an (incorrect) error in my ide
/// ```rs
/// # use memapi::type_props::{SizedProps, Thin};
///
/// fn safe<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub trait Thin: core::ptr::Pointee<Metadata = ()> + core::marker::PointeeSized {}

#[cfg(feature = "metadata")]
impl<P: core::ptr::Pointee<Metadata = ()>> Thin for P {}
