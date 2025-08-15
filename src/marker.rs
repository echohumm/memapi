/// Unsafe marker trait for types that can be copied, including unsized types such as slices.
///
/// # Safety
///
/// Implementing `UnsizedCopy` indicates the type's memory representation can be duplicated without
/// violating soundness or causing double frees.
pub unsafe trait UnsizedCopy {}

// SAFETY: Any `T` which is `Copy` is also `UnsizedCopy`.
unsafe impl<T: Copy> UnsizedCopy for T {}
// SAFETY: And so are slices containing copyable T.
unsafe impl<T: Copy> UnsizedCopy for [T] {}
// SAFETY: `str == [u8]` and `u8: Copy`.
unsafe impl UnsizedCopy for str {}
#[cfg(feature = "c_str")]
// SAFETY: `CStr == [u8]`
unsafe impl UnsizedCopy for core::ffi::CStr {}
#[cfg(feature = "std")]
// SAFETY: `OsStr == [u8]`
unsafe impl UnsizedCopy for std::ffi::OsStr {}
#[cfg(feature = "std")]
// SAFETY: `Path == OsStr == [u8]`
unsafe impl UnsizedCopy for std::path::Path {}

// TODO: add derive macros or smth for these
// TODO: better solution than making them all unsafe

#[cfg(all(not(feature = "metadata"), not(feature = "sized_hierarchy")))]
/// Trait indicating that a type has no metadata.
///
/// This usually means `Self: Sized` or `Self` is `extern`.
///
/// # Safety
///
/// Implementors must ensure this type has no metadata (`<Self as Pointee>::Metadata = ()`).
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::Thin};
///
/// fn never_panics<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub unsafe trait Thin {}

#[cfg(all(feature = "metadata", not(feature = "sized_hierarchy")))]
/// Trait indicating that a type has no metadata.
///
/// This usually means `Self: Sized` or `Self` is `extern`.
///
/// # Safety
///
/// This is safe to implement in this configuration; however, because the actually-unsafe
/// version exists when both `metadata` and `sized_hierarchy` are disabled, this trait
/// must still be marked `unsafe` for consistency across configurations.
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::Thin};
///
/// fn never_panics<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub unsafe trait Thin: core::ptr::Pointee<Metadata = ()> {}

#[cfg(all(feature = "metadata", feature = "sized_hierarchy"))]
/// Trait indicating that a type has no metadata and may or may not have a size.
///
/// # Safety
///
/// This is safe to implement in this configuration; however, because the actually-unsafe
/// version exists when both `metadata` and `sized_hierarchy` are disabled, this trait
/// must still be marked `unsafe` for consistency across configurations.
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::Thin};
///
/// fn never_panics<T: Thin>() {
///     assert_eq!(<&T>::SZ, usize::SZ)
/// }
/// ```
pub unsafe trait Thin:
    core::ptr::Pointee<Metadata = ()> + core::marker::PointeeSized
{
}

#[cfg(all(not(feature = "metadata"), not(feature = "sized_hierarchy")))]
/// Trait indicating that a type has `usize` metadata.
///
/// # Safety
///
/// Implementors must ensure this type has `usize` metadata (`<Self as Pointee>::Metadata = usize`).
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::SizeMeta};
///
/// fn never_panics<T: SizeMeta>() {
///    assert_eq!(<&T>::SZ, usize::SZ * 2)
/// }
/// ```
pub unsafe trait SizeMeta {}

#[cfg(all(not(feature = "metadata"), feature = "sized_hierarchy"))]
/// Trait indicating that a type has `usize` metadata.
///
/// # Safety
///
/// Implementors must ensure this type has `usize` metadata (`<Self as Pointee>::Metadata = usize`).
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::SizeMeta};
///
/// fn never_panics<T: SizeMeta>() {
///    assert_eq!(<&T>::SZ, usize::SZ * 2)
/// }
/// ```
pub unsafe trait SizeMeta: core::marker::MetaSized {}

#[cfg(all(feature = "metadata", not(feature = "sized_hierarchy")))]
/// Trait indicating that a type has `usize` metadata.
///
/// # Safety
///
/// This is safe to implement in this configuration; however, because the actually-unsafe version
/// exists when `metadata` is disabled, this trait must still be marked `unsafe` for consistency
/// across configurations.
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::SizeMeta};
///
/// fn never_panics<T: SizeMeta>() {
///    assert_eq!(<&T>::SZ, usize::SZ * 2)
/// }
/// ```
pub unsafe trait SizeMeta: core::ptr::Pointee<Metadata = usize> {}

#[cfg(all(feature = "metadata", feature = "sized_hierarchy"))]
/// Trait indicating that a type has `usize` metadata.
///
/// # Safety
///
/// This is safe to implement in this configuration; however, because the actually-unsafe version
/// exists when `metadata` is disabled, this trait must still be marked `unsafe` for consistency
/// across configurations.
///
/// # Example
///
/// ```
/// # use memapi::{type_props::SizedProps, marker::SizeMeta};
///
/// fn never_panics<T: SizeMeta>() {
///     assert_eq!(<&T>::SZ, usize::SZ * 2)
/// }
/// ```
pub unsafe trait SizeMeta:
    core::ptr::Pointee<Metadata = usize> + core::marker::MetaSized
{
}

#[cfg(feature = "metadata")]
// SAFETY: `P: Pointee<Metadata = ()>`
unsafe impl<P: core::ptr::Pointee<Metadata = ()> + ?Sized> Thin for P {}

#[cfg(feature = "metadata")]
// SAFETY: `P: Pointee<Metadata = usize>`
unsafe impl<P: core::ptr::Pointee<Metadata = usize> + ?Sized> SizeMeta for P {}
