#![allow(unused_qualifications, missing_docs)]

use alloc::alloc::Layout;
use core::{
    mem::{align_of, align_of_val, size_of, size_of_val},
    ptr::NonNull,
};
use crate::helpers::dangling_nonnull;

/// The maximum value of a `usize` with no high bit.
///
/// Equivalent to `usize::MAX >> 1` or `isize::MAX as usize`.
pub const USIZE_MAX_NO_HIGH_BIT: usize = usize::MAX >> 1;

/// A trait containing constants for sized types.
pub trait SizedProps: Sized {
    /// The size of the type.
    const SZ: usize = size_of::<Self>();
    /// The alignment of the type.
    const ALIGN: usize = align_of::<Self>();
    /// The memory layout for the type.
    const LAYOUT: Layout = unsafe { Layout::from_size_align_unchecked(Self::SZ, Self::ALIGN) };

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
/// Trait for unsized types whose metadata is `usize` (e.g., slices, `str`).
///
/// # Safety
///
/// The implementor guarantees that the `ALIGN` constant accurately represents the alignment
/// requirement of the type in any safe context and that the type's pointee metadata is `usize`.
pub unsafe trait VarSized {
    /// The alignment of the type.
    const ALIGN: usize;
}

#[cfg(feature = "metadata")]
/// Trait for unsized types whose metadata is `usize` (e.g., slices, `str`).
///
/// # Safety
///
/// The implementor guarantees that the `ALIGN` constant accurately represents the
/// alignment requirement of the type in any safe context.
pub unsafe trait VarSized: core::ptr::Pointee<Metadata = usize> {
    /// The alignment of the type.
    const ALIGN: usize;
}

unsafe impl<T> VarSized for [T] {
    const ALIGN: usize = T::ALIGN;
}

unsafe impl VarSized for str {
    const ALIGN: usize = u8::ALIGN;
}

#[cfg(feature = "c_str")]
unsafe impl VarSized for core::ffi::CStr {
    const ALIGN: usize = u8::ALIGN;
}
#[cfg(feature = "std")]
// `OsStr == [u8]` and `[u8]: VarSized`
unsafe impl VarSized for std::ffi::OsStr {
    const ALIGN: usize = u8::ALIGN;
}

#[cfg(feature = "std")]
unsafe impl VarSized for std::path::Path {
    const ALIGN: usize = u8::ALIGN;
}

// not associated to reduce clutter, and so they can be const

/// Creates a dangling, zero-length, [`NonNull`] pointer with the proper alignment.
#[must_use]
pub const fn varsized_dangling_nonnull<T: ?Sized + VarSized>() -> NonNull<T> {
    varsized_nonnull_from_raw_parts(unsafe { dangling_nonnull(T::ALIGN) }, 0)
}

#[must_use]
pub const fn varsized_dangling_pointer<T: ?Sized + VarSized>() -> *mut T {
    varsized_pointer_from_raw_parts(unsafe { dangling_nonnull(T::ALIGN).as_ptr() }, 0)
}

/// Creates a `NonNull<T>` from a pointer and a `usize` size metadata.
#[must_use]
#[inline]
pub const fn varsized_nonnull_from_raw_parts<T: ?Sized + VarSized>(
    p: NonNull<u8>,
    meta: usize,
) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(varsized_pointer_from_raw_parts(p.as_ptr(), meta)) }
}

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
