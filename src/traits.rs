use {
    crate::{Layout, error::AllocError, helpers::alloc_then},
    core::{
        cmp::Ordering,
        ptr::{self, NonNull}
    }
};

// TODO: try to remove Dealloc requirement from Grow/Shrink and by ext., Realloc
/// A memory allocation interface.
pub trait Alloc {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `layout` has a size of zero.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        // SAFETY: alloc returns at least layout.size() allocated bytes
        unsafe {
            alloc_then(self, layout, (), |p, ()| {
                ptr::write_bytes(p.as_ptr(), 0, layout.size());
                p
            })
        }
    }
}

/// A memory allocation interface which can also deallocate memory.
pub trait Dealloc: Alloc {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if `layout.size() == 0`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `layout` must describe exactly the same block.
    ///
    /// # Panics
    ///
    /// Some implementations may choose to panic if `ptr` or `layout` are invalid.
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);
}

/// A memory allocation interface which can also grow allocations.
pub trait Grow: Alloc + Dealloc {
    /// Grow the given block to a new, larger layout.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] if `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, Bytes::Uninitialized)
    }

    /// Grows the given block to a new, larger layout, zeroing any newly allocated bytes.
    ///
    /// Returns the new pointer, possibly reallocated elsewhere.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::GrowSmallerNewLayout`] in `new_layout.size() < old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        grow(self, ptr, old_layout, new_layout, Bytes::Zeroed)
    }
}

/// A memory allocation interface which can also shrink allocations.
pub trait Shrink: Alloc + Dealloc {
    /// Shrink the given block to a new, smaller layout.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block of memory allocated using this allocator.
    /// - `old_layout` must describe exactly the same block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ShrinkLargerNewLayout`] if `new_layout.size() > old_layout.size()`.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        shrink(self, ptr, old_layout, new_layout)
    }
}

/// A memory allocation interface which can arbitrarily resize allocations.
pub trait Realloc: Grow + Shrink {
    /// Reallocates a block, growing or shrinking as needed.
    ///
    ///
    /// On grow, preserves existing contents up to `old_layout.size()`, and
    /// on shrink, truncates to `new_layout.size()`.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, Bytes::Uninitialized)
    }

    /// Reallocates a block, growing or shrinking as needed, zeroing any newly
    /// allocated bytes.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a block previously allocated with this allocator.
    /// - `old_layout` must describe exactly that block.
    ///
    /// # Errors
    ///
    /// - [`AllocError::AllocFailed`] if allocation fails.
    /// - [`AllocError::ZeroSizedLayout`] if `new_layout` has a size of zero.
    ///
    /// On failure, the original memory won't be deallocated or modified.
    #[cfg_attr(miri, track_caller)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        ralloc(self, ptr, old_layout, new_layout, Bytes::Zeroed)
    }
}

/// A memory allocation interface which can allocate and deallocate.
///
/// This exists solely because it reads more nicely than `A: Dealloc`; the two are the same.
pub trait BasicAlloc: Alloc + Dealloc {}
/// A memory allocation interface which can allocate, deallocate, and arbitrarily resize
/// allocations.
///
/// This exists solely because it reads more nicely than `A: Realloc`; the two are the same.
pub trait FullAlloc: Realloc + Grow + Shrink + Alloc + Dealloc {}

impl<A: Alloc + Dealloc> BasicAlloc for A {}
impl<A: Realloc + Grow + Shrink + Alloc + Dealloc> FullAlloc for A {}

#[allow(clippy::inline_always)]
impl<A: Alloc + ?Sized> Alloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        (**self).alloc(layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        (**self).zalloc(layout)
    }
}
#[allow(clippy::inline_always)]
impl<A: Dealloc + ?Sized> Dealloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        (**self).dealloc(ptr, layout);
    }
}
// TODO: idk if this duplicated code is worth it either
#[allow(clippy::inline_always)]
impl<A: Grow + ?Sized> Grow for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        (**self).grow(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn zgrow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        (**self).zgrow(ptr, old_layout, new_layout)
    }
}
#[allow(clippy::inline_always)]
impl<A: Shrink + ?Sized> Shrink for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        (**self).shrink(ptr, old_layout, new_layout)
    }
}
#[allow(clippy::inline_always)]
impl<A: Realloc + ?Sized> Realloc for &A {
    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn realloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        (**self).realloc(ptr, old_layout, new_layout)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline(always)]
    unsafe fn rezalloc(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, AllocError> {
        (**self).rezalloc(ptr, old_layout, new_layout)
    }
}

#[cfg(feature = "std")]
impl Alloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        crate::helpers::null_q_zsl_check(
            layout,
            // SAFETY: System::alloc is only called after the layout is verified non-zero-sized.
            |layout| unsafe {
                alloc::alloc::GlobalAlloc::alloc(self, crate::layout_handle(layout))
            },
            crate::helpers::null_q_dyn
        )
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    fn zalloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        crate::helpers::null_q_zsl_check(
            layout,
            // SAFETY: System::alloc_zeroed is only called after the layout is verified
            //  non-zero-sized.
            |layout| unsafe {
                alloc::alloc::GlobalAlloc::alloc_zeroed(self, crate::layout_handle(layout))
            },
            crate::helpers::null_q_dyn
        )
    }
}
#[cfg(feature = "std")]
impl Dealloc for std::alloc::System {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            alloc::alloc::GlobalAlloc::dealloc(self, ptr.as_ptr(), crate::layout_handle(layout));
        }
    }
}
#[cfg(feature = "std")]
impl Grow for std::alloc::System {}
#[cfg(feature = "std")]
impl Shrink for std::alloc::System {}
#[cfg(feature = "std")]
impl Realloc for std::alloc::System {}

// TODO: make this whole system better

#[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
#[cfg_attr(miri, track_caller)]
unsafe fn grow<A: Grow + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => grow_unchecked(a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                grow_unchecked(&a, ptr, old_layout, new_layout, b)
            }
        }
        Ordering::Greater => {
            Err(AllocError::GrowSmallerNewLayout(old_layout.size(), new_layout.size()))
        }
    }
}

#[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
#[cfg_attr(miri, track_caller)]
unsafe fn shrink<A: Shrink + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => {
            Err(AllocError::ShrinkLargerNewLayout(old_layout.size(), new_layout.size()))
        }
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                shrink_unchecked(&a, ptr, old_layout, new_layout)
            }
        }
        Ordering::Greater => shrink_unchecked(a, ptr, old_layout, new_layout)
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function doesn't check for layout validity.
/// Callers must ensure `new_layout.size()` is greater than `old_layout.size()`.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(miri, track_caller)]
unsafe fn grow_unchecked<A: Grow + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, AllocError> {
    let old_size = old_layout.size();
    let new_ptr = match b {
        Bytes::Uninitialized => tri!(do a.alloc(new_layout)),
        Bytes::Zeroed => tri!(do a.zalloc(new_layout))
    };

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
    if old_size != 0 {
        a.dealloc(ptr, old_layout);
    }

    Ok(new_ptr)
}

/// Internal helper to shrink the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function doesn't check for layout validity.
/// Callers must ensure `new_layout.size()` is greater than `old_layout.size()`.
#[cfg_attr(miri, track_caller)]
unsafe fn shrink_unchecked<A: Shrink + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout
) -> Result<NonNull<u8>, AllocError> {
    let new_ptr = tri!(do a.alloc(new_layout));

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
    if old_layout.size() != 0 {
        a.dealloc(ptr, old_layout);
    }

    Ok(new_ptr)
}

#[allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]
#[cfg_attr(miri, track_caller)]
unsafe fn ralloc<A: Realloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, AllocError> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => grow_unchecked(&a, ptr, old_layout, new_layout, b),
        Ordering::Greater => shrink_unchecked(&a, ptr, old_layout, new_layout),
        Ordering::Equal => {
            if new_layout.align() == old_layout.align() {
                Ok(ptr)
            } else {
                grow_unchecked(&a, ptr, old_layout, new_layout, b)
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Bytes {
    /// Uninitialized bytes.
    Uninitialized,
    /// Zeroed bytes.
    Zeroed
}
