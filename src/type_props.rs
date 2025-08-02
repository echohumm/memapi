#![allow(unused_qualifications)]

use alloc::alloc::Layout;
use core::{
    mem::{align_of, align_of_val, size_of, size_of_val},
    ptr::NonNull,
};

/// The maximum value of a `usize` with no high bit.
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
    unsafe fn layout(&self) -> Layout;

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

/// Implements [`PtrProps`] for a pointer type.
macro_rules! impl_ptr_props {
	($($name:ty $(,$to_ptr:ident)?)*) => {
		$(
		impl<T: ?Sized> PtrProps<T> for $name {
			unsafe fn size(&self) -> usize {
				// We use &*(*val) (?.to_ptr()?) to convert any primitive pointer type to a
                //  reference.
				// This is kind of a hack, but it lets us avoid *_of_val_raw, which is unstable.
				size_of_val::<T>(&*(*self)$(.$to_ptr())?)
			}

			unsafe fn align(&self) -> usize {
				align_of_val::<T>(&*(*self)$(.$to_ptr())?)
			}

			unsafe fn layout(&self) -> Layout {
				Layout::from_size_align_unchecked(
					self.size(),
					self.align()
				)
			}

			#[cfg(feature = "metadata")]
			unsafe fn metadata(&self) -> <T as core::ptr::Pointee>::Metadata {
				core::ptr::metadata(&*(*self)$(.$to_ptr())?)
			}
		}
		)*
	}
}

impl_ptr_props!(
    *const T
    *mut T

    &T
    &mut T

    NonNull<T>, as_ptr

    alloc::boxed::Box<T>
    alloc::rc::Rc<T>
    alloc::sync::Arc<T>
);

#[cfg(not(feature = "metadata"))]
/// Trait for unsized types whose metadata is `usize` (e.g., slices, `str`).
///
/// # Safety
///
/// The implementor guarantees that the `ALIGN` constant accurately represents the
/// alignment requirement of the type in any safe context.
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

unsafe impl VarSized for str {
    const ALIGN: usize = u8::ALIGN;
}

#[cfg(feature = "c_str")]
unsafe impl VarSized for core::ffi::CStr {
    const ALIGN: usize = u8::ALIGN;
}
#[cfg(feature = "std")]
// `OsStr == [u8]` and `[u8]: UnsizedCopy`
unsafe impl VarSized for std::ffi::OsStr {
    const ALIGN: usize = u8::ALIGN;
}

#[cfg(feature = "std")]
unsafe impl VarSized for std::path::Path {
    const ALIGN: usize = u8::ALIGN;
}

unsafe impl<T> VarSized for [T] {
    const ALIGN: usize = T::ALIGN;
}

// not associated to reduce clutter, and so they can be const

#[cfg(feature = "metadata")]
/// Creates a dangling, zero-length, [`NonNull`] pointer with the proper alignment.
///
#[must_use]
#[inline]
pub const fn varsized_dangling_nonnull<T: ?Sized + VarSized>() -> NonNull<T> {
    // SAFETY: `ALIGN` is guaranteed to be a valid alignment for `Self`.
    unsafe { NonNull::from_raw_parts(crate::helpers::dangling_nonnull(T::ALIGN), 0) }
}

#[cfg(feature = "metadata")]
/// Creates a dangling, zero-length mutable pointer with the proper alignment.
#[must_use]
#[inline]
pub const fn varsized_dangling_ptr_mut<T: ?Sized + VarSized>() -> *mut T {
    core::ptr::from_raw_parts_mut(T::ALIGN as *mut (), 0)
}

#[cfg(feature = "metadata")]
/// Creates a dangling, zero-length immutable pointer with the proper alignment.
#[must_use]
#[inline]
pub const fn varsized_dangling_ptr<T: ?Sized + VarSized>() -> *const T {
    core::ptr::from_raw_parts(T::ALIGN as *const (), 0)
}
