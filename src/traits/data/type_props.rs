use {
    crate::{helpers::USIZE_MAX_NO_HIGH_BIT, layout::Layout},
    ::core::{
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
    const LAYOUT: Layout = Layout::new::<Self>();

    /// Whether the type is zero-sized.
    const IS_ZST: bool = Self::SZ == 0;

    /// The largest safe length for a `[Self]`.
    const MAX_SLICE_LEN: usize = match Self::SZ {
        0 => usize::MAX,
        sz => USIZE_MAX_NO_HIGH_BIT / sz
    };

    /// A valid, [dangling](::core::ptr::dangling) pointer for this layout's alignment.
    ///
    /// # Safety
    ///
    /// This pointer is non-null and correctly aligned for this type, but should not be
    /// dereferenced.
    // SAFETY: an alignment cannot be 0 so it is not a null pointer; caller
    const DANGLING_PTR: NonNull<Self> = unsafe { NonNull::new_unchecked(Self::ALN as *mut Self) };
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
    #[must_use]
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
    #[must_use]
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
    #[must_use]
    #[inline]
    unsafe fn layout(&self) -> Layout {
        // SAFETY: caller guarantees
        let sz = unsafe { self.sz() };
        // SAFETY: above
        let aln = unsafe { self.aln() };
        // SAFETY: size and alignment of a value cannot be invalid for a layout
        unsafe { Layout::from_size_align_unchecked(sz, aln) }
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
    #[must_use]
    unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata;

    #[cfg(feature = "metadata")]
    /// <placeholder>
    ///
    /// # Safety
    #[must_use]
    fn varsized_metadata(&self) -> usize
    where
        T: VarSized
    {
        // SAFETY: requirements are passed on to the caller
        unsafe { self.metadata() }
    }

    #[cfg(not(feature = "metadata"))]
    /// <placeholder>
    ///
    /// # Safety
    #[must_use]
    fn varsized_metadata(&self) -> usize
    where
        T: VarSized;

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
    #[must_use]
    #[inline]
    unsafe fn is_zero_sized(&self) -> bool {
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
    #[must_use]
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
                #[inline]
                unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
                    ::core::ptr::metadata(&*(*self))
                }
                #[cfg(not(feature = "metadata"))]
                #[inline]
                fn varsized_metadata(&self) -> usize where T: VarSized {
                    split_varsized_ptr(*self).1
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
                #[inline]
                unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
                    ::core::ptr::metadata(*self)
                }
                #[cfg(not(feature = "metadata"))]
                #[inline]
                fn varsized_metadata(&self) -> usize where T: VarSized {
                    split_varsized_ptr(*self).1
                }
            }
        )*
    };
}

macro_rules! impl_ptr_props_deref {
    ($($name:ty),* $(,)?) => {
        $(
            #[allow(unused_qualifications)]
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
                #[inline]
                unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
                    ::core::ptr::metadata(&**self)
                }
                #[cfg(not(feature = "metadata"))]
                #[inline]
                fn varsized_metadata(&self) -> usize where T: VarSized {
                    split_varsized_ptr(&**self).1
                }
            }
        )*
    };
}

impl_ptr_props_raw! { *const T, *mut T }
impl_ptr_props_identity! { &T, &mut T }
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl_ptr_props_deref! {
    ::stdalloc::boxed::Box<T>,
    ::stdalloc::rc::Rc<T>,
    ::stdalloc::sync::Arc<T>,
}
#[cfg(any(not(feature = "no_alloc"), feature = "std"))]
impl<T: ::core::clone::Clone> PtrProps<T> for ::stdalloc::borrow::Cow<'_, T> {
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
    #[cfg(not(feature = "metadata"))]
    fn varsized_metadata(&self) -> usize
    where
        T: VarSized
    {
        #[allow(unused_imports)] use ::core::panic;

        ::core::unreachable!("`Cow<T>` can never be unsized as it requires `T: Clone`")
    }
}

impl<T: ?Sized> PtrProps<T> for NonNull<T> {
    #[inline]
    unsafe fn sz(&self) -> usize {
        size_of_val::<T>(&(*self.as_ptr()))
    }

    #[inline]
    unsafe fn aln(&self) -> usize {
        align_of_val::<T>(&(*self.as_ptr()))
    }

    #[cfg(feature = "metadata")]
    #[inline]
    unsafe fn metadata(&self) -> <T as ::core::ptr::Pointee>::Metadata {
        ::core::ptr::metadata(self.as_ptr())
    }
    #[cfg(not(feature = "metadata"))]
    #[inline]
    fn varsized_metadata(&self) -> usize
    where
        T: VarSized
    {
        self.as_ptr().varsized_metadata()
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

    #[::rustversion::since(1.61)]
    /// A valid, [dangling](::core::ptr::dangling) pointer for this layout's alignment.
    ///
    /// Note that this only exists on Rust versions 1.61 and above.
    ///
    /// # Safety
    ///
    /// This pointer is non-null and correctly aligned for this type, but should not be
    /// dereferenced.
    // SAFETY: the implementor of VarSized guarantees the ALN is valid.
    const DANGLING_PTR: NonNull<Self> =
        varsized_nonnull_from_parts(<Self::SubType as SizedProps>::DANGLING_PTR.cast(), 0);
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

    #[::rustversion::since(1.61)]
    /// A valid, [dangling](::core::ptr::dangling) pointer for this layout's alignment.
    ///
    /// Note that this only exists on Rust versions 1.61 and above.
    ///
    /// # Safety
    ///
    /// This pointer is non-null and correctly aligned for this type, but should not be
    /// dereferenced.
    // SAFETY: the implementor of VarSized guarantees the ALN is valid.
    const DANGLING_PTR: NonNull<Self> =
        varsized_nonnull_from_parts(<Self::SubType as SizedProps>::DANGLING_PTR.cast(), 0);
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

/// Creates a <code>[NonNull]\<T\></code> from a pointer and a `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[::rustversion::attr(since(1.61), const)]
#[must_use]
#[inline]
pub fn varsized_nonnull_from_parts<T: ?Sized + VarSized>(
    p: NonNull<u8>,
    meta: usize
) -> NonNull<T> {
    // SAFETY: `p` was already non-null, so it with different meta must also be nn.
    unsafe { NonNull::new_unchecked(varsized_ptr_from_parts_mut(p.as_ptr(), meta)) }
}

#[::rustversion::since(1.83)]
/// Creates a `*mut T` from a pointer and a `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[must_use]
#[inline]
pub const fn varsized_ptr_from_parts_mut<T: ?Sized + VarSized>(p: *mut u8, meta: usize) -> *mut T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe {
        *((&::core::ptr::slice_from_raw_parts_mut::<T::SubType>(p.cast(), meta)
            as *const *mut [T::SubType])
            .cast::<*mut T>())
    }
}
#[::rustversion::before(1.83)]
/// Creates a `*mut T` from a pointer and a `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[must_use]
#[inline]
#[::rustversion::attr(since(1.61), const)]
pub fn varsized_ptr_from_parts_mut<T: ?Sized + VarSized>(p: *mut u8, meta: usize) -> *mut T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe { crate::helpers::union_transmute::<(*mut u8, usize), *mut T>((p, meta)) }
}

#[::rustversion::since(1.64)]
/// Creates a `*mut T` from a pointer and a `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[must_use]
#[inline]
pub const fn varsized_ptr_from_parts<T: ?Sized + VarSized>(p: *const u8, meta: usize) -> *const T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe {
        *((&::core::ptr::slice_from_raw_parts::<T::SubType>(p.cast(), meta)
            as *const *const [T::SubType])
            .cast::<*const T>())
    }
}
#[::rustversion::before(1.64)]
/// Creates a `*mut T` from a pointer and a `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[::rustversion::attr(since(1.61), const)]
#[must_use]
#[inline]
pub fn varsized_ptr_from_parts<T: ?Sized + VarSized>(p: *const u8, meta: usize) -> *const T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe { crate::helpers::union_transmute::<(*const u8, usize), *const T>((p, meta)) }
}

/// Splits a `*const T` where `T` has `usize` metadata into a `*const u8` and the `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[::rustversion::attr(since(1.61), const)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[must_use]
#[inline]
pub fn split_varsized_ptr<T: ?Sized + VarSized>(p: *const T) -> (*const u8, usize) {
    // SAFETY: Varsized trait requirement requires T::Metadata == usize; as of the current rust
    // version, *mut T where T has usize metadata equates to a (*mut (), usize).
    unsafe { crate::helpers::union_transmute::<*const T, (*const u8, usize)>(p) }
}

/// Splits a `*mut T` where `T` has `usize` metadata into a `*mut u8` and the `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[::rustversion::attr(since(1.61), const)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[must_use]
#[inline]
pub fn split_varsized_ptr_mut<T: ?Sized + VarSized>(p: *mut T) -> (*mut u8, usize) {
    // SAFETY: see split_varsized_ptr
    unsafe { crate::helpers::union_transmute::<*mut T, (*mut u8, usize)>(p) }
}

/// Splits a <code>[NonNull]\<T\></code> where `T` has `usize` metadata into a
/// <code>[NonNull]\<u8\></code> and the `usize` metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
#[::rustversion::attr(since(1.61), const)]
#[must_use]
#[inline]
pub fn split_varsized_nonnull<T: ?Sized + VarSized>(p: NonNull<T>) -> (NonNull<u8>, usize) {
    // SAFETY: see split_varsized_ptr; NonNull<T> == *mut T internally
    unsafe { crate::helpers::union_transmute::<NonNull<T>, (NonNull<u8>, usize)>(p) }
}
