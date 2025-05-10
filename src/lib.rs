//! `memapi` provides a minimal, `no_std`-friendly memory allocation interface
//! for managing raw buffers, suitable for use in collections.
//!
//! This crate exports:
//!
//! - [`Alloc`], a trait defining basic allocate, deallocate, grow, and shrink operations.
//! - [`DefaultAlloc`], a zero-cost wrapper delegating to the global allocator.
//! - [`AllocError`], an enum of possible error cases.
//!
//! # Examples
//!
//! ```rust
//! # use memapi::{Alloc, DefaultAlloc, AllocError};
//! # use core::alloc::Layout;
//! # use core::ptr::NonNull;
//!
//! let allocator = DefaultAlloc;
//! let layout = Layout::from_size_align(64, 8).unwrap();
//! // Allocate 64 bytes
//! let ptr: NonNull<u8> = allocator.alloc(layout).expect("alloc failed");
//! unsafe { allocator.dealloc(ptr, layout) };
//! ```

#![no_std]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![allow(unsafe_op_in_unsafe_fn)]

extern crate alloc;

#[cfg(test)]
mod tests;

use core::{
    alloc::Layout,
    cmp::Ordering,
    error::Error,
    fmt::{Display, Formatter},
    ptr::{self, NonNull},
};

const fn layout_or_sz_align<T>(n: usize) -> Result<Layout, (usize, usize)> {
    let (sz, align) = (size_of::<T>(), align_of::<T>());

    if sz != 0 && n > unsafe { (isize::MAX as usize + 1).unchecked_sub(align) } / sz {
        return Err((sz, align));
    }

    let arr_sz = unsafe { sz.unchecked_mul(n) };

    unsafe { Ok(Layout::from_size_align_unchecked(arr_sz, align)) }
}

/// Default allocator, delegating to the global allocator.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultAlloc;

/// A minimal memory allocation interface.
///
/// This trait does _not_ require `Self: Allocator` and is `no_std`-compatible.
pub trait Alloc: Sized {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Returns a non-null pointer on success, or [`AllocError::AllocFailed`].
    #[track_caller]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a block of memory for `count` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_count<T>(&self, count: usize) -> Result<NonNull<T>, AllocError> {
        let layout =
            layout_or_sz_align::<T>(count).map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc(layout)
            .map(NonNull::cast)
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// Returns a non-null pointer on success, or [`AllocError::AllocFailed`].
    #[track_caller]
    fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a zeroed block of memory for `count` instances of `T`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_count_zeroed<T>(&self, count: usize) -> Result<NonNull<T>, AllocError> {
        let layout =
            layout_or_sz_align::<T>(count).map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_zeroed(layout)
            .map(NonNull::cast)
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`], filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// Returns a non-null pointer on success, or [`AllocError::AllocFailed`].
    #[track_caller]
    fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a block of memory for `count` instances of `T`, filled with bytes
    /// initialized to `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_count_filled<T>(&self, count: usize, n: u8) -> Result<NonNull<T>, AllocError> {
        let layout =
            layout_or_sz_align::<T>(count).map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_filled(layout, n)
            .map(NonNull::cast)
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Attempts to allocate a block of memory fitting the given [`Layout`] and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// Returns [`AllocError::AllocFailed`] if the allocation fails.
    #[track_caller]
    fn alloc_patterned<F: Fn(usize) -> u8>(
        &self,
        layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a block of memory for `count` instances of `T` and
    /// fill it by calling `pattern(i)` for each byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::LayoutError`] if the computed layout is invalid.
    #[track_caller]
    #[inline]
    fn alloc_count_patterned<T, F: Fn(usize) -> u8>(&self, count: usize, pattern: F) -> Result<NonNull<T>, AllocError> {
        let layout =
            layout_or_sz_align::<T>(count).map_err(|(sz, align)| AllocError::LayoutError(sz, align))?;
        self.alloc_patterned(layout, pattern)
            .map(NonNull::cast)
            .map_err(|_| AllocError::AllocFailed(layout))
    }

    /// Deallocates a previously allocated block.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    #[track_caller]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);

    /// Grow the given block to a new, larger layout.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::None,
        )
    }

    /// Grows the given block to a new, larger layout, zeroing newly allocated space.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::Zero,
        )
    }

    /// Grow the given block to a new, larger layout, filling any newly allocated
    /// bytes by calling `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    unsafe fn grow_patterned<F: Fn(usize) -> u8>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
    }

    /// Grows the given block to a new, larger layout, filling newly allocated space with `n`.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    fn grow_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        grow(
            self,
            ptr,
            old_layout,
            new_layout,
            AllocPattern::<fn(usize) -> u8>::All(n),
        )
    }

    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkBiggerNewLayout`] if `new_layout.size() > old_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    #[track_caller]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        shrink(self, ptr, old_layout, new_layout)
    }

    /// Reallocate a block, growing or shrinking as needed (no zeroing).
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_layout.size()`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            grow_unchecked(
                self,
                ptr,
                old_layout,
                new_layout,
                AllocPattern::<fn(usize) -> u8>::None,
            )
        } else {
            shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, zeroing any newly
    /// allocated bytes.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    unsafe fn realloc_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<u8>, AllocError> {
        self.realloc_filled(ptr, old_layout, new_layout, 0)
    }

    /// Reallocate a block, growing or shrinking as needed, filling any new
    /// bytes by calling `pattern(i)` for each new byte index `i`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    unsafe fn realloc_patterned<F: Fn(usize) -> u8>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            grow_unchecked(self, ptr, old_layout, new_layout, AllocPattern::Fn(pattern))
        } else {
            shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }

    /// Reallocate a block, growing or shrinking as needed, filling any newly
    /// allocated bytes with `n`.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    #[track_caller]
    unsafe fn realloc_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<NonNull<u8>, AllocError> {
        if new_layout.size() > old_layout.size() {
            grow_unchecked(
                self,
                ptr,
                old_layout,
                new_layout,
                AllocPattern::<fn(usize) -> u8>::All(n),
            )
        } else {
            shrink_unchecked(self, ptr, old_layout, new_layout)
        }
    }
}

#[cfg(feature = "nightly")]
pub(crate) mod nightly {
    use super::{Alloc, AllocError, DefaultAlloc};
    use alloc::alloc::{Allocator, Global, Layout};
    use core::ptr::NonNull;

    unsafe impl Allocator for DefaultAlloc {
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::allocate(&Global, layout)
        }

        fn allocate_zeroed(
            &self,
            layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::allocate_zeroed(&Global, layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            Allocator::deallocate(&Global, ptr.cast(), layout);
        }

        unsafe fn grow(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::grow(&Global, ptr.cast(), old_layout, new_layout)
        }

        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::grow_zeroed(&Global, ptr.cast(), old_layout, new_layout)
        }

        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
            Allocator::shrink(&Global, ptr.cast(), old_layout, new_layout)
        }
    }

    impl<A: Allocator> Alloc for A {
        fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            Allocator::allocate(self, layout)
                .map_err(|_| AllocError::AllocFailed(layout))
                .map(NonNull::cast)
        }

        fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            Allocator::allocate_zeroed(self, layout)
                .map_err(|_| AllocError::AllocFailed(layout))
                .map(NonNull::cast)
        }

        fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
            Allocator::allocate(self, layout)
                .map_err(|_| AllocError::AllocFailed(layout))
                .map(|ptr| {
                    let ptr = ptr.cast::<u8>();
                    unsafe {
                        ptr.write_bytes(n, layout.size());
                    }
                    ptr
                })
        }

        fn alloc_patterned<F: Fn(usize) -> u8>(
            &self,
            layout: Layout,
            pattern: F,
        ) -> Result<NonNull<u8>, AllocError> {
            Allocator::allocate(self, layout)
                .map_err(|_| AllocError::AllocFailed(layout))
                .map(|ptr| {
                    let ptr = ptr.cast::<u8>();
                    for i in 0..layout.size() {
                        unsafe {
                            ptr.as_ptr().add(i).write(pattern(i));
                        }
                    }
                    ptr
                })
        }

        unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
            Allocator::deallocate(self, ptr.cast(), layout);
        }
    }
}

#[cfg(not(feature = "nightly"))]
pub(crate) mod fallback {
    use super::{Alloc, AllocError};
    use alloc::alloc::{
        Layout, alloc as raw_alloc, alloc_zeroed as raw_alloc_zeroed, dealloc as raw_dealloc,
    };
    use core::ptr::NonNull;

    impl Alloc for super::DefaultAlloc {
        fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            NonNull::new(unsafe { raw_alloc(layout) }).ok_or(AllocError::AllocFailed(layout))
        }

        fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
            NonNull::new(unsafe { raw_alloc_zeroed(layout) }).ok_or(AllocError::AllocFailed(layout))
        }

        fn alloc_filled(&self, layout: Layout, n: u8) -> Result<NonNull<u8>, AllocError> {
            let ptr = NonNull::new(unsafe { raw_alloc(layout).cast::<u8>() })
                .ok_or(AllocError::AllocFailed(layout))?;
            unsafe {
                ptr.write_bytes(n, layout.size());
            }
            Ok(ptr)
        }

        fn alloc_patterned<F: Fn(usize) -> u8>(
            &self,
            layout: Layout,
            pattern: F,
        ) -> Result<NonNull<u8>, AllocError> {
            let ptr = NonNull::new(unsafe { raw_alloc(layout).cast::<u8>() })
                .ok_or(AllocError::AllocFailed(layout))?;
            for i in 0..layout.size() {
                unsafe {
                    ptr.as_ptr().add(i).write(pattern(i));
                }
            }
            Ok(ptr)
        }

        unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
            raw_dealloc(ptr.as_ptr(), layout);
        }
    }
}

/// Errors for allocation operations.
#[derive(Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AllocError {
    LayoutError(usize, usize),
    /// Underlying allocator failed to allocate.
    AllocFailed(Layout),
    /// Attempted to grow to a smaller layout.
    GrowSmallerNewLayout(usize, usize),
    /// Attempted to shrink to a larger layout.
    ShrinkBiggerNewLayout(usize, usize),
}

impl Display for AllocError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            AllocError::LayoutError(sz, align) => {
                write!(f, "computed invalid layout: size: {sz}, align: {align}")
            }
            AllocError::AllocFailed(l) => write!(f, "allocation failed for layout: {l:?}"),
            AllocError::GrowSmallerNewLayout(old, new) => write!(
                f,
                "attempted to grow from a size of {old} to a smaller size of {new}"
            ),
            AllocError::ShrinkBiggerNewLayout(old, new) => write!(
                f,
                "attempted to shrink from a size of {old} to a larger size of {new}"
            ),
        }
    }
}

impl Error for AllocError {}

#[inline]
#[track_caller]
fn grow<A: Alloc, F: Fn(usize) -> u8>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => unsafe { grow_unchecked(a, ptr, old_layout, new_layout, pattern) },
        Ordering::Equal => Ok(ptr),
        Ordering::Greater => Err(AllocError::GrowSmallerNewLayout(
            old_layout.size(),
            new_layout.size(),
        )),
    }
}

#[inline]
#[track_caller]
fn shrink<A: Alloc>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => Err(AllocError::ShrinkBiggerNewLayout(
            old_layout.size(),
            new_layout.size(),
        )),
        Ordering::Equal => Ok(ptr),
        Ordering::Greater => unsafe { shrink_unchecked(a, ptr, old_layout, new_layout) },
    }
}

#[inline]
#[track_caller]
unsafe fn grow_unchecked<A: Alloc, F: Fn(usize) -> u8>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    pattern: AllocPattern<F>,
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = match pattern {
        AllocPattern::None => a.alloc(new_layout)?.cast::<u8>(),
        AllocPattern::Fn(f) => a.alloc_patterned(new_layout, f)?,
        AllocPattern::Zero => a.alloc_zeroed(new_layout)?.cast::<u8>(),
        AllocPattern::All(n) => a.alloc_filled(new_layout, n)?.cast::<u8>(),
    };
    unsafe {
        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_layout.size());
        a.dealloc(ptr, old_layout);
    }
    Ok(new_ptr)
}

#[inline]
#[track_caller]
unsafe fn shrink_unchecked<A: Alloc>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = a.alloc(new_layout)?.cast::<u8>();
    unsafe {
        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
        a.dealloc(ptr, old_layout);
    }
    Ok(new_ptr)
}

enum AllocPattern<F: Fn(usize) -> u8> {
    None,
    Zero,
    All(u8),
    Fn(F),
}
