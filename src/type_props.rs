use crate::helpers::dangling_nonnull;
use alloc::alloc::Layout;
use core::{
    mem::{align_of, align_of_val, size_of, size_of_val},
    ptr::NonNull,
};

/// The maximum value of a `usize` with no high bit.
///
/// Equivalent to `usize::MAX >> 1` or `isize::MAX as usize`.
///
#[cfg_attr(
    target_pointer_width = "64",
    doc = "Exact value: `9_223_372_036_854_775_807`"
)]
#[cfg_attr(target_pointer_width = "32", doc = "Exact value: `2_147_483_647`")]
// no way this ever gets hit, but oh well
#[cfg_attr(target_pointer_width = "16", doc = "Exact value: `32_767`")]
pub const USIZE_MAX_NO_HIGH_BIT: usize = usize::MAX >> 1;

/// A `usize` in which only the high bit is set.
///
/// Equivalent to `usize::MAX ^ (usize::MAX >> 1)` or `usize::MAX << usize::BITS - 1`.
///
#[cfg_attr(
    target_pointer_width = "64",
    doc = "Exact value: `9_223_372_036_854_775_807`"
)]
#[cfg_attr(target_pointer_width = "32", doc = "Exact value: `2_147_483_647`")]
#[cfg_attr(target_pointer_width = "16", doc = "Exact value: `32_767`")]
pub const USIZE_HIGH_BIT: usize = usize::MAX ^ (usize::MAX >> 1);

/// A trait containing constants for sized types.
pub trait SizedProps: Sized {
    /// The size of the type.
    const SZ: usize = size_of::<Self>();
    /// The alignment of the type.
    const ALN: usize = align_of::<Self>();
    /// The memory layout for the type.
    // SAFETY: this is the same as Layout::new::<T>().
    const LAYOUT: Layout = unsafe { Layout::from_size_align_unchecked(Self::SZ, Self::ALN) };

    /// Whether the type is zero-sized.
    const IS_ZST: bool = Self::SZ == 0;

    /// The largest safe length for a `[Self]`.
    const MAX_SLICE_LEN: usize = match Self::SZ {
        0 => usize::MAX,
        sz => USIZE_MAX_NO_HIGH_BIT / sz,
    };
}

impl<T> SizedProps for T {}

/// A trait providing methods for pointers to provide the properties of their pointees.
pub trait PtrProps<T: ?Sized> {
    /// Gets the size of the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid as a reference.
    unsafe fn size(&self) -> usize;
    /// Gets the alignment of the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid as a reference.
    unsafe fn align(&self) -> usize;
    /// Gets the memory layout for the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid as a reference.
    #[inline]
    unsafe fn layout(&self) -> Layout {
        Layout::from_size_align_unchecked(self.size(), self.align())
    }

    #[cfg(feature = "metadata")]
    /// Gets the metadata of the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid as a reference.
    unsafe fn metadata(&self) -> <T as core::ptr::Pointee>::Metadata;

    /// Checks whether the value is zero-sized.
    ///
    /// # Safety
    ///
    /// The pointer must be valid as a reference.
    unsafe fn is_zst(&self) -> bool {
        self.size() == 0
    }

    /// Gets the largest safe length for a slice containing copies of `self`.
    ///
    /// # Safety
    ///
    /// The pointer must be valid as a reference.
    // this has almost no real use case as far as i can tell
    unsafe fn max_slice_len(&self) -> usize {
        match self.size() {
            0 => usize::MAX,
            sz => USIZE_MAX_NO_HIGH_BIT / sz,
        }
    }
}

macro_rules! impl_ptr_props_raw {
    ($($name:ty),* $(,)?) => {
        $(
            impl<T: ?Sized> PtrProps<T> for $name {
                #[inline]
                unsafe fn size(&self) -> usize {
                    size_of_val::<T>(&**self)
                }
                #[inline]
                unsafe fn align(&self) -> usize {
                    align_of_val::<T>(&**self)
                }
                #[cfg(feature = "metadata")]
                unsafe fn metadata(&self) -> <T as core::ptr::Pointee>::Metadata {
                    core::ptr::metadata(&*(*self))
                }
            }
        )*
    };
}

macro_rules! impl_ptr_props_identity {
    ($($name:ty),* $(,)?) => {
        $(
            impl<T: ?Sized> PtrProps<T> for $name {
                #[inline]
                unsafe fn size(&self) -> usize {
                    size_of_val::<T>(*self)
                }
                #[inline]
                unsafe fn align(&self) -> usize {
                    align_of_val::<T>(*self)
                }
                #[cfg(feature = "metadata")]
                unsafe fn metadata(&self) -> <T as core::ptr::Pointee>::Metadata {
                    core::ptr::metadata(*self)
                }
            }
        )*
    };
}

macro_rules! impl_ptr_props_as_ref {
    ($($name:ty),* $(,)?) => {
        $(
            impl<T: ?Sized> PtrProps<T> for $name {
                #[inline]
                unsafe fn size(&self) -> usize {
                    size_of_val::<T>(self.as_ref())
                }
                #[inline]
                unsafe fn align(&self) -> usize {
                    align_of_val::<T>(self.as_ref())
                }
                #[cfg(feature = "metadata")]
                unsafe fn metadata(&self) -> <T as core::ptr::Pointee>::Metadata {
                    core::ptr::metadata(self.as_ref())
                }
            }
        )*
    };
}

impl_ptr_props_raw! { *const T, *mut T }
impl_ptr_props_identity! { &T, &mut T }
impl_ptr_props_as_ref! {
    alloc::boxed::Box<T>,
    alloc::rc::Rc<T>,
    alloc::sync::Arc<T>
}

impl<T: ?Sized> PtrProps<T> for NonNull<T> {
    #[inline]
    unsafe fn size(&self) -> usize {
        size_of_val::<T>(&*self.as_ptr())
    }
    #[inline]
    unsafe fn align(&self) -> usize {
        align_of_val::<T>(&*self.as_ptr())
    }
    #[cfg(feature = "metadata")]
    unsafe fn metadata(&self) -> <T as core::ptr::Pointee>::Metadata {
        core::ptr::metadata(&*self.as_ptr())
    }
}

#[cfg(not(feature = "metadata"))]
/// Trait for unsized types that use `usize` metadata (for example, slices and `str`).
///
/// # Safety
///
/// Implementors must ensure that `Subtype` is the actual element type contained and that the `ALN`
/// constant accurately reflects the type's alignment requirement in all safe contexts.
pub unsafe trait VarSized {
    /// The element type.
    ///
    /// [`VarSized`] types are either slices of another type or include a slice tail; this is that
    /// element type.
    type Subtype: Sized + SizedProps;

    /// The alignment of the type.
    ///
    /// Override this if the type contains more than just a slice of its
    /// [`Subtype`](VarSized::Subtype).
    const ALN: usize = Self::Subtype::ALN;
}

#[cfg(feature = "metadata")]
/// Trait for unsized types that use `usize` metadata (for example, slices and `str`).
///
/// # Safety
///
/// Implementors must ensure that `Subtype` is the actual element type contained and that the `ALN`
/// constant accurately reflects the type's alignment requirement in all safe contexts.
pub unsafe trait VarSized: crate::marker::SizeMeta {
    /// The element type.
    ///
    /// [`VarSized`] types are either slices of another type or include a slice tail; this is that
    /// element type.
    type Subtype: Sized + SizedProps;

    /// The alignment of the type.
    ///
    /// Override this if the type contains more than just a slice of its
    /// [`Subtype`](VarSized::Subtype).
    const ALN: usize = Self::Subtype::ALN;
}

unsafe impl<T> VarSized for [T] {
    type Subtype = T;
}

unsafe impl VarSized for str {
    type Subtype = u8;
}

#[cfg(feature = "c_str")]
unsafe impl VarSized for core::ffi::CStr {
    type Subtype = u8;
}
#[cfg(feature = "std")]
unsafe impl VarSized for std::ffi::OsStr {
    type Subtype = u8;
}

#[cfg(feature = "std")]
unsafe impl VarSized for std::path::Path {
    type Subtype = u8;
}

// not associated to reduce clutter, and so they can be const

// TODO: use const_if! (cant rn because it doesnt support relaxed bounds or multiple bounds

// SAFETY of below: the implementor of VarSized guarantees the ALN is valid.

#[cfg(feature = "const_extras")]
/// Creates a dangling, zero-length, [`NonNull`] pointer with the proper alignment.
#[must_use]
pub const fn varsized_dangling_nonnull<T: ?Sized + VarSized>() -> NonNull<T> {
    varsized_nonnull_from_raw_parts(unsafe { dangling_nonnull(T::ALN) }, 0)
}

#[cfg(not(feature = "const_extras"))]
/// Creates a dangling, zero-length, [`NonNull`] pointer with the proper alignment.
#[must_use]
pub fn varsized_dangling_nonnull<T: ?Sized + VarSized>() -> NonNull<T> {
    varsized_nonnull_from_raw_parts(unsafe { dangling_nonnull(T::ALN) }, 0)
}

#[cfg(feature = "const_extras")]
/// Creates a dangling, zero-length [`NonNull`] pointer with the proper alignment.
#[must_use]
pub const fn varsized_dangling_pointer<T: ?Sized + VarSized>() -> *mut T {
    varsized_pointer_from_raw_parts(unsafe { dangling_nonnull(T::ALN).as_ptr() }, 0)
}

#[cfg(not(feature = "const_extras"))]
/// Creates a dangling, zero-length [`NonNull`] pointer with the proper alignment.
#[must_use]
pub fn varsized_dangling_pointer<T: ?Sized + VarSized>() -> *mut T {
    varsized_pointer_from_raw_parts(unsafe { dangling_nonnull(T::ALN).as_ptr() }, 0)
}

#[cfg(feature = "const_extras")]
/// Creates a `NonNull<T>` from a pointer and a `usize` size metadata.
#[must_use]
#[inline]
pub const fn varsized_nonnull_from_raw_parts<T: ?Sized + VarSized>(
    p: NonNull<u8>,
    meta: usize,
) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(varsized_pointer_from_raw_parts(p.as_ptr(), meta)) }
}

#[cfg(not(feature = "const_extras"))]
/// Creates a `NonNull<T>` from a pointer and a `usize` size metadata.
#[must_use]
#[inline]
pub fn varsized_nonnull_from_raw_parts<T: ?Sized + VarSized>(
    p: NonNull<u8>,
    meta: usize,
) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(varsized_pointer_from_raw_parts(p.as_ptr(), meta)) }
}

#[cfg(feature = "const_extras")]
/// Creates a `*mut T` from a pointer and a `usize` size metadata.
#[must_use]
#[inline]
pub const fn varsized_pointer_from_raw_parts<T: ?Sized + VarSized>(
    p: *mut u8,
    meta: usize,
) -> *mut T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe {
        // i hate this so much
        *((&(p, meta)) as *const (*mut u8, usize)).cast::<*mut T>()
    }
}

#[cfg(not(feature = "const_extras"))]
/// Creates a `*mut T` from a pointer and a `usize` size metadata.
#[must_use]
#[inline]
pub fn varsized_pointer_from_raw_parts<T: ?Sized + VarSized>(p: *mut u8, meta: usize) -> *mut T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe {
        // i hate this so much
        *((&(p, meta)) as *const (*mut u8, usize)).cast::<*mut T>()
    }
}
