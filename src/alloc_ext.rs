use crate::{Alloc, AllocError, UnsizedCopy};
use core::{
	alloc::Layout,
	ptr::{self, NonNull, metadata},
};

/// Extension methods for the core [`Alloc`] trait, providing convenient
/// routines to allocate, initialize, clone, copy, and deallocate sized
/// and unsized types.
///
/// These helpers simplify common allocation patterns by combining
/// `alloc`, writes, drops, and deallocations for various data shapes.
pub trait AllocExt: Alloc {
	/// Allocates uninitialized memory for a single `T` and writes `data` into it.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	fn alloc_write<T>(&self, data: T) -> Result<NonNull<T>, AllocError> {
		match self.alloc(Layout::new::<T>()) {
			Ok(ptr) => Ok(unsafe {
				let ptr = ptr.cast();
				ptr.write(data);
				ptr
			}),
			Err(e) => Err(e),
		}
	}
	
	// FIXME: switch to CloneToUninit when stable
	/// Allocates uninitialized memory for a single `T` and clones `data` into it.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	fn alloc_clone_to<T: Clone>(&self, data: &T) -> Result<NonNull<T>, AllocError> {
		match self.alloc(Layout::new::<T>()) {
			Ok(ptr) => Ok(unsafe {
				let ptr = ptr.cast();
				ptr.write(data.clone());
				ptr
			}),
			Err(e) => Err(e),
		}
	}

	/// Allocates uninitialized memory for a slice of `T` and clones each element.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	fn alloc_clone_slice_to<T: Clone>(&self, data: &[T]) -> Result<NonNull<[T]>, AllocError> {
		match self.alloc(Layout::for_value(data)) {
			Ok(ptr) => Ok(unsafe {
				let ptr = ptr.cast();
				for (i, elem) in data.iter().enumerate() {
					ptr.add(i).write(elem.clone());
				}
				NonNull::slice_from_raw_parts(ptr, data.len())
			}),
			Err(e) => Err(e),
		}
	}

	/// Deallocates a previously cloned or written slice of `T`.
	///
	/// # Safety
	///
	/// - `slice_ptr` must point to a block of memory allocated using this allocator.
	#[track_caller]
	#[inline]
	unsafe fn dealloc_slice<T>(&self, slice_ptr: NonNull<[T]>) {
		self.dealloc(slice_ptr.cast::<u8>(), Layout::for_value(&*slice_ptr.as_ptr()));
	}

	/// Drops and deallocates a previously cloned or written slice of `T`.
	///
	/// # Safety
	///
	/// - `slice_ptr` must point to a block of memory allocated using this allocator, be valid for 
	///   reads and writes, aligned, and a valid `T`.
	#[track_caller]
	#[inline]
	unsafe fn drop_and_dealloc_slice<T>(&self, slice_ptr: NonNull<[T]>) {
		slice_ptr.drop_in_place();
		self.dealloc_slice(slice_ptr);
	}

	/// Allocates and copies an unsized `T` by reference, returning a `NonNull<T>`.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	fn alloc_copy_ref_to<T: ?Sized + UnsizedCopy>(
		&self,
		data: &T,
	) -> Result<NonNull<T>, AllocError> {
		unsafe { self.alloc_copy_ref_to_unchecked(data) }
	}

	/// Allocates and copies an unsized `T` by raw pointer, returning a `NonNull<T>`.
	/// 
	/// # Safety
	/// 
	/// - The caller must ensure `data` is a valid pointer to copy from.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	unsafe fn alloc_copy_ptr_to<T: ?Sized + UnsizedCopy>(
		&self,
		data: *const T,
	) -> Result<NonNull<T>, AllocError> {
		unsafe { self.alloc_copy_ptr_to_unchecked(data) }
	}

	/// Allocates and copies an unsized `T` by reference without requiring 
	/// `T: `[`UnsizedCopy`](UnsizedCopy), returning a `NonNull<T>`.
	///
	/// # Safety
	///
	/// - The caller must ensure `data` is safe to copy.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	unsafe fn alloc_copy_ref_to_unchecked<T: ?Sized>(
		&self,
		data: &T,
	) -> Result<NonNull<T>, AllocError> {
		match self.alloc(Layout::for_value(data)) {
			Ok(ptr) => Ok({
				ptr.copy_from_nonoverlapping(*ptr::from_ref(data).cast(), size_of_val::<T>(data));
				NonNull::from_raw_parts(ptr, metadata(&raw const *data))
			}),
			Err(e) => Err(e),
		}
	}

	/// Allocates and copies an unsized `T` by raw pointer without requiring 
	/// `T: `[`UnsizedCopy`](UnsizedCopy), returning a `NonNull<T>`.
	///
	/// # Safety
	///
	/// - The caller must ensure `data` is safe to copy.
	///
	/// # Errors
	///
	/// - [`AllocError::AllocFailed`] if allocation fails.
	#[track_caller]
	#[inline]
	unsafe fn alloc_copy_ptr_to_unchecked<T: ?Sized + UnsizedCopy>(
		&self,
		data: *const T,
	) -> Result<NonNull<T>, AllocError> {
		match self.alloc(Layout::for_value(&*data)) {
			Ok(ptr) => Ok({
				ptr.copy_from_nonoverlapping(*data.cast(), size_of_val::<T>(&*data));
				NonNull::from_raw_parts(ptr, metadata(data))
			}),
			Err(e) => Err(e),
		}
	}
}

impl<A: Alloc> AllocExt for A {}
