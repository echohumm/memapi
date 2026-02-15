use {
    crate::{helpers::USIZE_MAX_NO_HIGH_BIT, layout::Layout},
    ::core::{
        clone::Clone,
        convert::AsRef,
        marker::Sized,
        mem::{align_of, align_of_val, size_of, size_of_val},
        ptr::NonNull
    }
};

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
        sz => USIZE_MAX_NO_HIGH_BIT / sz
    };
}

impl<T> SizedProps for T {}

/// A trait providing methods for pointers to provide the properties of their pointees.
pub trait PtrProps<T: ?Sized> {
    /// Gets the size of the value.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self` is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    ///
    /// References are always valid.
    unsafe fn sz(&self) -> usize;
    /// Gets the alignment of the value.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self` is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    ///
    /// References are always valid.
    unsafe fn aln(&self) -> usize;
    /// Gets the memory layout for the value.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self` is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    ///
    /// References are always valid.
    #[inline]
    unsafe fn layout(&self) -> Layout {
        Layout::from_size_align_unchecked(self.sz(), self.aln())
    }

    #[cfg(feature = "metadata")]
    /// Gets the metadata of the value.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self` is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    ///
    /// References are always valid.
    unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata;

    /// Checks whether the value is zero-sized.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self` is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    ///
    /// References are always valid.
    unsafe fn is_zst(&self) -> bool {
        self.sz() == 0
    }

    /// Gets the largest safe length for a slice containing copies of `self`.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self` is:
    /// - non-null
    /// - non-dangling
    /// - aligned
    ///
    /// References are always valid.
    unsafe fn max_slice_len(&self) -> usize {
        match self.sz() {
            0 => usize::MAX,
            sz => USIZE_MAX_NO_HIGH_BIT / sz
        }
    }
}

/// Implements `PtrProps` for raw pointers.
macro_rules! impl_ptr_props_raw {
    ($($name:ty),* $(,)?) => {
        $(
            impl<T: ?Sized> PtrProps<T> for $name {
                #[inline]
                unsafe fn sz(&self) -> usize {
                    size_of_val::<T>(&**self)
                }
                #[inline]
                unsafe fn aln(&self) -> usize {
                    align_of_val::<T>(&**self)
                }
                #[cfg(feature = "metadata")]
                unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
                    ::core::ptr::metadata(&*(*self))
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
                unsafe fn sz(&self) -> usize {
                    size_of_val::<T>(*self)
                }
                #[inline]
                unsafe fn aln(&self) -> usize {
                    align_of_val::<T>(*self)
                }
                #[cfg(feature = "metadata")]
                unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
                    ::core::ptr::metadata(*self)
                }
            }
        )*
    };
}

macro_rules! impl_ptr_props_as_ref {
    ($($name:ty),* $(,)?) => {
        $(
            #[allow(unused_qualifications)]
            impl<T: ?Sized> PtrProps<T> for $name {
                #[inline]
                unsafe fn sz(&self) -> usize {
                    size_of_val::<T>(self.as_ref())
                }
                #[inline]
                unsafe fn aln(&self) -> usize {
                    align_of_val::<T>(self.as_ref())
                }
                #[cfg(feature = "metadata")]
                unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
                    ::core::ptr::metadata(self.as_ref())
                }
            }
        )*
    };
}

impl_ptr_props_raw! { *const T, *mut T }
impl_ptr_props_identity! { &T, &mut T }
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl_ptr_props_as_ref! {
    ::stdalloc::boxed::Box<T>,
    ::stdalloc::rc::Rc<T>,
    ::stdalloc::sync::Arc<T>,
}
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl<T: Clone> PtrProps<T> for ::stdalloc::borrow::Cow<'_, T> {
    #[inline]
    unsafe fn sz(&self) -> usize {
        T::SZ
    }
    #[inline]
    unsafe fn aln(&self) -> usize {
        T::ALN
    }
    #[cfg(feature = "metadata")]
    unsafe fn metadata(&self) {}
}

impl<T: ?Sized> PtrProps<T> for NonNull<T> {
    #[inline]
    unsafe fn sz(&self) -> usize {
        size_of_val::<T>(&*self.as_ptr())
    }

    #[inline]
    unsafe fn aln(&self) -> usize {
        align_of_val::<T>(&*self.as_ptr())
    }

    #[cfg(feature = "metadata")]
    unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
        ::core::ptr::metadata(&*self.as_ptr())
    }
}

#[cfg(not(feature = "metadata"))]
/// Trait for unsized types that use `usize` metadata (for example, slices and `str`).
///
/// # Safety
///
/// The implementor must ensure that [`SubType`](VarSized::SubType) is the actual element type
/// contained, that the [`ALN`](VarSized::ALN) constant accurately reflects the type's alignment
/// requirement in all safe contexts, and that this type has `usize` metadata (`<Self as
/// Pointee>::Metadata = usize`).
pub unsafe trait VarSized {
    /// The element type.
    ///
    /// [`VarSized`] types are either slices of another type or include a slice tail; this is that
    /// element type.
    type SubType: Sized;

    /// The alignment of the type.
    ///
    /// Override this if the type contains more than just a slice of its
    /// [`SubType`](VarSized::SubType).
    const ALN: usize = Self::SubType::ALN;
}

#[cfg(feature = "metadata")]
/// Trait for unsized types that use `usize` metadata (for example, slices and `str`).
///
/// # Safety
///
/// The implementor must ensure that [`SubType`](VarSized::SubType) is the actual element type
/// contained, and that the [`ALN`](VarSized::ALN) constant accurately reflects the type's alignment
/// requirement in all safe contexts.
pub unsafe trait VarSized: ::core::ptr::Pointee<Metadata = usize> {
    /// The element type.
    ///
    /// [`VarSized`] types are either slices of another type or include a slice tail; this is that
    /// element type.
    type SubType: Sized + SizedProps;

    /// The alignment of the type.
    ///
    /// Override this if the type contains more than just a slice of its
    /// [`SubType`](VarSized::SubType).
    const ALN: usize = Self::SubType::ALN;
}

// TODO: derive macro/other macros to help implement this would be very useful

#[cfg(not(feature = "metadata"))]
/// Trait for unsized _structs_ that have a [`VarSized`] tail.
///
/// # Safety
///
/// The implementor must ensure that [`Tail`](VarSizedStruct::Tail) is the actual tail type
/// contained, that the [`ALN`](VarSizedStruct::ALN) constant accurately reflects the type's
/// alignment requirement in all safe contexts, and that this type has `usize` metadata (`<Self as
/// Pointee>::Metadata = usize`).
pub unsafe trait VarSizedStruct {
    /// The [`VarSized`] tail type.
    ///
    /// [`VarSizedStruct`] types are unsized structs that contain a [`VarSized`] tail; this is that
    /// tail type.
    type Tail: VarSized;

    /// The alignment of the type.
    ///
    /// # How to determine
    ///
    /// The alignment of a [`VarSizedStruct`] is determined by its fields and its `repr` attribute.
    ///
    /// ## Fields
    ///
    /// Consider all fields of the struct, including the unsized tail. For the tail field, use
    /// its [`VarSized::ALN`] as its alignment.
    ///
    /// ## Determination based on `#[repr]`
    ///
    /// ### Rust default / `#[repr(Rust)]` / `#[repr(C)]`
    ///
    /// The alignment of the struct is the maximum alignment of all of its fields. (<code>ALN =
    /// max([align_of]::\<Field1\>(), [align_of]::\<Field2\>(), ...,
    /// <[Self::Tail](VarSizedStruct::Tail) as [VarSized]>::[ALN](VarSized::ALN))</code>)
    ///
    /// ### `#[repr(packed)]`
    ///
    /// The alignment of the struct is always 1.
    ///
    /// ### `#[repr(packed(N))]`
    ///
    /// The alignment of the struct is the minimum of `N` and the maximum alignment of all of its
    /// fields. (<code>ALN = min(N, max([align_of]::\<Field1\>(), [align_of]::\<Field2\>(), ...,
    /// <[Self::Tail](VarSizedStruct::Tail) as [VarSized]>::[ALN](VarSized::ALN)))</code>)
    ///
    /// ### `#[repr(align(N))]`
    ///
    /// If `#[repr(align(N))]` is used, the alignment of the struct is the maximum of `N` and the
    /// alignment it would otherwise have. (<code>ALN = max(N, [align_of]::\<Field1\>(),
    /// [align_of]::\<Field2\>(), ..., <[Self::Tail](VarSizedStruct::Tail) as
    /// [VarSized]>::[ALN](VarSized::ALN))</code>).
    const ALN: usize;
}

#[cfg(feature = "metadata")]
/// Trait for unsized _structs_ that have a [`VarSized`] tail.
///
/// # Safety
///
/// The implementor must ensure that [`Tail`](VarSizedStruct::Tail) is the actual tail type
/// contained, and that the [`ALN`](VarSizedStruct::ALN) constant accurately reflects the type's
/// alignment requirement in all safe contexts.
pub unsafe trait VarSizedStruct: ::core::ptr::Pointee<Metadata = usize> {
    /// The [`VarSized`] tail type.
    ///
    /// [`VarSizedStruct`] types are unsized structs that contain a [`VarSized`] tail; this is that
    /// tail type.
    type Tail: VarSized;

    /// The alignment of the type.
    ///
    /// # How to determine
    ///
    /// The alignment of a [`VarSizedStruct`] is determined by its fields and its `repr` attribute.
    ///
    /// ## Fields
    ///
    /// Consider all fields of the struct, including the unsized tail. For the tail field, use
    /// its [`VarSized::ALN`] as its alignment.
    ///
    /// ## Determination based on `#[repr]`
    ///
    /// ### Rust default / `#[repr(Rust)]` / `#[repr(C)]`
    ///
    /// The alignment of the struct is the maximum alignment of all of its fields. (<code>ALN =
    /// max([align_of]::\<Field1\>(), [align_of]::\<Field2\>(), ...,
    /// <[Self::Tail](VarSizedStruct::Tail) as [VarSized]>::[ALN](VarSized::ALN))</code>)
    ///
    /// ### `#[repr(packed)]`
    ///
    /// The alignment of the struct is always 1.
    ///
    /// ### `#[repr(packed(N))]`
    ///
    /// The alignment of the struct is the minimum of `N` and the maximum alignment of all of its
    /// fields. (<code>ALN = min(N, max([align_of]::\<Field1\>(), [align_of]::\<Field2\>(), ...,
    /// <[Self::Tail](VarSizedStruct::Tail) as [VarSized]>::[ALN](VarSized::ALN)))</code>)
    ///
    /// ### `#[repr(align(N))]`
    ///
    /// If `#[repr(align(N))]` is used, the alignment of the struct is the maximum of `N` and the
    /// alignment it would otherwise have. (<code>ALN = max(N, [align_of]::\<Field1\>(),
    /// [align_of]::\<Field2\>(), ..., <[Self::Tail](VarSizedStruct::Tail) as
    /// [VarSized]>::[ALN](VarSized::ALN))</code>).
    const ALN: usize;
}

// SAFETY: `[T]: Pointee<Metadata = usize> + MetaSized`
unsafe impl<T> VarSized for [T] {
    type SubType = T;
}

// SAFETY: `str = [u8]`
unsafe impl VarSized for str {
    type SubType = u8;
}

#[cfg(all(feature = "c_str", not(feature = "std")))]
// SAFETY: `CStr = [u8]`
unsafe impl VarSized for ::core::ffi::CStr {
    type SubType = u8;
}
#[cfg(feature = "std")]
// SAFETY: `OsStr = [u8]`
unsafe impl VarSized for ::std::ffi::OsStr {
    type SubType = u8;
}

#[cfg(feature = "std")]
// SAFETY: `Path = OsStr = [u8]`
unsafe impl VarSized for ::std::path::Path {
    type SubType = u8;
}

// SAFETY: obviously any VarSized struct is VarSized, we just propagate the values.
unsafe impl<T: VarSizedStruct> VarSized for T {
    type SubType = <T::Tail as VarSized>::SubType;

    const ALN: usize = <T as VarSizedStruct>::ALN;
}

// anysized system didn't work well enough for me to actually keep it.
