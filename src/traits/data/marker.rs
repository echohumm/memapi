use ::core::marker::Copy;

/// Unsafe marker trait for types that can be copied, including unsized types such as slices.
///
/// # Safety
///
/// The implementor must ensure `Self` has a memory representation which can be duplicated without
/// violating soundness or causing double frees.
pub unsafe trait UnsizedCopy {}

// SAFETY: Any `T` which is `Copy` is also `UnsizedCopy`.
unsafe impl<T: Copy> UnsizedCopy for T {}
// SAFETY: And so are slices containing copyable T.
unsafe impl<T: Copy> UnsizedCopy for [T] {}
// SAFETY: `str == [u8]` and `u8: Copy`, so, above.
unsafe impl UnsizedCopy for str {}
#[::rustversion::since(1.64)]
#[cfg(not(feature = "std"))]
// SAFETY: `CStr == [u8]`
unsafe impl UnsizedCopy for ::core::ffi::CStr {}
#[cfg(feature = "std")]
// SAFETY: `CStr == [u8]`
unsafe impl UnsizedCopy for ::std::ffi::CStr {}
#[cfg(feature = "std")]
// SAFETY: `OsStr == [u8]`
unsafe impl UnsizedCopy for ::std::ffi::OsStr {}
#[cfg(feature = "std")]
// SAFETY: `Path == OsStr == [u8]`
unsafe impl UnsizedCopy for ::std::path::Path {}

#[cfg(not(feature = "metadata"))]
/// Trait indicating that a type has no metadata.
///
/// This usually means `Self: Sized` or `Self` is `extern`.
///
/// # Safety
///
/// The implementor must ensure this type has no metadata (`<Self as Pointee>::Metadata = ()`).
///
/// # Example
///
/// ```
/// # use memapi2::traits::data::{marker::Thin, type_props::SizedProps};
///
/// fn never_panics<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub unsafe trait Thin {}

#[cfg(feature = "metadata")]
/// Trait indicating that a type has no metadata.
///
/// This usually means `Self: Sized` or `Self` is `extern`.
///
/// # Safety
///
/// This is safe to implement in this configuration; however, because the actually unsafe
/// version exists when `metadata` is disabled, this trait must still be marked `unsafe` for
/// consistency across configurations.
///
/// # Example
///
/// ```
/// # use memapi2::traits::{data::type_props::SizedProps, data::marker::Thin};
///
/// fn never_panics<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub unsafe trait Thin: ::core::ptr::Pointee<Metadata = ()> {}

#[cfg(feature = "metadata")]
// SAFETY: `P: Pointee<Metadata = ()>`
unsafe impl<P: ::core::ptr::Pointee<Metadata = ()> + ?::core::marker::Sized> Thin for P {}
