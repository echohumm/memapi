#![allow(clippy::missing_errors_doc, missing_docs)]

use crate::{
    error::AllocError, helpers::alloc_write, type_props::varsized_dangling_nonnull,
    type_props::PtrProps, Alloc, DefaultAlloc,
};
use core::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::forget,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

/// A single value of type `T`, allocated using `A`.
///
/// This functions similarly to a [`Box`](alloc::boxed::Box).
pub struct HeapVal<T: ?Sized, A: Alloc = DefaultAlloc> {
    ptr: NonNull<T>,
    alloc: A,
    _marker: PhantomData<T>,
}

impl<T> HeapVal<T> {
    /// Constructs a new [`HeapVal`] with the given value in the default allocator.
    #[inline]
    pub fn new(val: T) -> Result<HeapVal<T>, AllocError> {
        HeapVal::new_in(val, DefaultAlloc)
    }

    // todo: other variants which this just calls
    pub fn clone_from_ref(val: &T) -> Result<Self, AllocError>
    where
        T: Clone,
    {
        HeapVal::clone_from_ref_in(val, DefaultAlloc)
    }
}

impl<T: ?Sized> HeapVal<T> {
    /// Constructs a new [`HeapVal`] by copying from a reference.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `val.size() == 0`.
    #[inline]
    pub fn copy_from_ref(val: &T) -> Result<HeapVal<T>, AllocError>
    where
        T: crate::marker::UnsizedCopy,
    {
        HeapVal::copy_from_ref_in(val, DefaultAlloc)
    }

    /// Constructs a new [`HeapVal`] by copying from a raw pointer.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `val.size() == 0`.
    ///
    /// # Safety
    ///
    /// The caller must ensure `val` points to a valid `T`.
    #[inline]
    pub unsafe fn copy_from_ptr(val: *const T) -> Result<HeapVal<T>, AllocError>
    where
        T: crate::marker::UnsizedCopy,
    {
        HeapVal::copy_from_ptr_in(val, DefaultAlloc)
    }

    /// Constructs a new [`HeapVal`] using the given pointer and the default allocator.
    ///
    /// # Safety
    ///
    /// The caller must ensure the given pointer points to a valid `T` allocated using the default
    /// allocator.
    #[must_use]
    #[inline]
    pub const unsafe fn from_raw(ptr: NonNull<T>) -> HeapVal<T> {
        HeapVal::from_raw_in(ptr, DefaultAlloc)
    }
}

impl<T, A: Alloc> HeapVal<T, A> {
    /// Constructs a new [`HeapVal`] with the given value, in the given allocator.
    #[inline]
    pub fn new_in(val: T, alloc: A) -> Result<HeapVal<T, A>, AllocError> {
        Ok(unsafe { HeapVal::from_raw_in(alloc_write(&alloc, val)?, alloc) })
    }

    pub fn clone_from_ref_in(val: &T, alloc: A) -> Result<HeapVal<T, A>, AllocError>
    where
        T: Clone,
    {
        Ok(unsafe { HeapVal::from_raw_in(alloc_write(&alloc, val.clone())?, alloc) })
    }

    pub const fn unwrap(self) -> T {
        let val = unsafe { self.ptr.read() };
        forget(self);
        val
    }
}

impl<T: Default, A: Alloc + Default> Default for HeapVal<T, A> {
    fn default() -> HeapVal<T, A> {
        HeapVal::new_in(T::default(), A::default()).expect("`HeapVal::default()` allocation failed")
    }
}

impl<T: Clone, A: Alloc + Clone> Clone for HeapVal<T, A> {
    fn clone(&self) -> HeapVal<T, A> {
        HeapVal::clone_from_ref_in(self.as_ref(), self.alloc.clone())
            .expect("`HeapVal::clone()` allocation failed")
    }
}

// impl<T: Clone, A: Alloc + Clone> Clone for HeapVal<[T], A> {
//     fn clone(&self) -> HeapVal<[T], A> {
//
//     }
// }

impl<T, A: Alloc + Default> From<T> for HeapVal<T, A> {
    fn from(val: T) -> HeapVal<T, A> {
        HeapVal::new_in(val, A::default()).expect("`HeapVal::<From<T>>::from()` allocation failed")
    }
}

impl<T: ?Sized, A: Alloc> HeapVal<T, A> {
    /// Constructs a [`HeapVal`] by allocating using the given allocator and copying from a
    /// reference.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `val.size() == 0`.
    #[inline]
    pub fn copy_from_ref_in(val: &T, alloc: A) -> Result<HeapVal<T, A>, AllocError>
    where
        T: crate::marker::UnsizedCopy,
    {
        unsafe { HeapVal::copy_from_ref_in_unchecked(val, alloc) }
    }

    /// Constructs a [`HeapVal`] by allocating using the given allocator and copying from a
    /// reference. This method has no `T: `[`crate::marker::UnsizedCopy`] bound.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `val.size() == 0`.
    ///
    /// # Safety
    ///
    /// The caller must ensure `val` is safe to copy.
    #[inline]
    pub unsafe fn copy_from_ref_in_unchecked(
        val: &T,
        alloc: A,
    ) -> Result<HeapVal<T, A>, AllocError> {
        HeapVal::copy_from_ptr_in_unchecked(val, alloc)
    }

    /// Constructs a [`HeapVal`] by allocating using the given allocator and copying from a
    /// raw pointer.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    ///
    /// # Safety
    ///
    /// The caller must ensure `val` points to a valid `T`
    #[inline]
    pub unsafe fn copy_from_ptr_in(val: *const T, alloc: A) -> Result<HeapVal<T, A>, AllocError>
    where
        T: crate::marker::UnsizedCopy,
    {
        HeapVal::copy_from_ptr_in_unchecked(val, alloc)
    }

    /// Constructs a [`HeapVal`] by allocating using the given allocator and copying from a
    /// reference. This method has no `T: `[`crate::marker::UnsizedCopy`] bound.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `val.size() == 0`.
    ///
    /// # Safety
    ///
    /// The caller must ensure `val` points to a valid, safe-to-copy `T`.
    #[inline]
    pub unsafe fn copy_from_ptr_in_unchecked(
        val: *const T,
        alloc: A,
    ) -> Result<HeapVal<T, A>, AllocError> {
        Ok(HeapVal::from_raw_in(
            crate::helpers::alloc_copy_ptr_to_unchecked(&alloc, val)?,
            alloc,
        ))
    }

    /// Constructs a new [`HeapVal`] using the given pointer and allocator.
    ///
    /// # Safety
    ///
    /// The caller must ensure the given pointer points to a valid `T` allocated using the given
    /// allocator.
    #[must_use]
    #[inline]
    pub const unsafe fn from_raw_in(ptr: NonNull<T>, alloc: A) -> HeapVal<T, A> {
        HeapVal {
            ptr,
            alloc,
            _marker: PhantomData,
        }
    }

    /// Destructor to drop the value and deallocate the memory.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn drop_and_dealloc(self) {
        unsafe {
            self.reset();
        }
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn reset(&self) {
        self.ptr.drop_in_place();
        self.alloc.dealloc(self.ptr.cast(), self.ptr.layout());
    }

    /// Destructor to drop the value, then zero and deallocate the memory.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn drop_zero_and_dealloc(self) {
        unsafe {
            self.reset_zero();
        }
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn reset_zero(&self) {
        self.ptr.drop_in_place();
        let layout = self.ptr.layout();
        self.ptr.cast::<u8>().write_bytes(0, layout.size());
        self.alloc.dealloc(self.ptr.cast(), layout);
    }

    /// Converts this [`HeapVal`] into a [`NonNull`] pointer to its value.
    #[inline]
    pub const fn into_ptr(self) -> NonNull<T> {
        let ptr = self.ptr;
        forget(self);
        ptr
    }

    #[inline]
    pub const fn as_ptr(&self) -> NonNull<T> {
        self.ptr
    }

    #[inline]
    pub const fn as_raw_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    #[inline]
    pub const fn as_mut_raw_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[must_use]
    #[inline]
    pub const fn leak<'a>(self) -> &'a mut T {
        let ptr = self.ptr;
        forget(self);
        unsafe { &mut *ptr.as_ptr() }
    }

    #[must_use]
    #[inline]
    pub const fn leak_with_alloc<'a>(self) -> (&'a mut T, A) {
        let ptr = self.ptr;
        let alloc = unsafe { (&raw const self.alloc).read() };
        forget(self);
        (unsafe { &mut *ptr.as_ptr() }, alloc)
    }
}

impl<T, A: Alloc + Default> Default for HeapVal<[T], A> {
    fn default() -> HeapVal<[T], A> {
        unsafe { HeapVal::from_raw_in(NonNull::<[T; 0]>::dangling(), A::default()) }
    }
}

impl<A: Alloc + Default> Default for HeapVal<str, A> {
    fn default() -> HeapVal<str, A> {
        unsafe { HeapVal::from_raw_in(varsized_dangling_nonnull::<str>(), A::default()) }
    }
}

impl<T: ?Sized, A: Alloc> Deref for HeapVal<T, A> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl<T: ?Sized, A: Alloc> DerefMut for HeapVal<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr.as_ptr() }
    }
}

impl<T: ?Sized, A: Alloc> AsRef<T> for HeapVal<T, A> {
    #[inline]
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: ?Sized, A: Alloc> AsMut<T> for HeapVal<T, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: ?Sized, A: Alloc> Borrow<T> for HeapVal<T, A> {
    #[inline]
    fn borrow(&self) -> &T {
        self
    }
}

impl<T: ?Sized, A: Alloc> BorrowMut<T> for HeapVal<T, A> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: ?Sized + Debug, A: Alloc> Debug for HeapVal<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        <T as Debug>::fmt(self, f)
    }
}

impl<T: ?Sized + Display, A: Alloc> Display for HeapVal<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        <T as Display>::fmt(self, f)
    }
}

impl<T: ?Sized + PartialEq, A: Alloc> PartialEq for HeapVal<T, A> {
    #[inline]
    fn eq(&self, other: &HeapVal<T, A>) -> bool {
        (**self).eq(&**other)
    }
}
impl<T: ?Sized + Eq, A: Alloc> Eq for HeapVal<T, A> {}

impl<T: ?Sized + PartialOrd, A: Alloc> PartialOrd for HeapVal<T, A> {
    fn partial_cmp(&self, other: &HeapVal<T, A>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}
impl<T: ?Sized + Ord, A: Alloc> Ord for HeapVal<T, A> {
    fn cmp(&self, other: &HeapVal<T, A>) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Hash, A: Alloc> Hash for HeapVal<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

#[cfg(all(feature = "drop_for_owned", not(feature = "zero_drop_for_owned")))]
impl<T: ?Sized, A: Alloc> Drop for HeapVal<T, A> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.reset();
        }
    }
}

#[cfg(feature = "zero_drop_for_owned")]
impl<T: ?Sized, A: Alloc> Drop for HeapVal<T, A> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.reset_zero();
        }
    }
}
