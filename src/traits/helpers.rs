use {
    crate::{Grow, Layout, Realloc, Shrink, error::Error},
    core::{
        cmp::Ordering,
        ptr::{self, NonNull}
    }
};

pub fn default_dealloc_panic(ptr: NonNull<u8>, layout: Layout, e: Error) -> ! {
    panic!(
        "deallocation of block at {:p} with layout {:?} failed: {}",
        ptr.as_ptr(),
        layout,
        e
    )
}

#[cfg_attr(miri, track_caller)]
pub unsafe fn grow<A: Grow + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, Error> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => grow_unchecked(a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            if new_layout.align() > old_layout.align() {
                grow_unchecked(&a, ptr, old_layout, new_layout, b)
            } else {
                Ok(ptr)
            }
        }
        Ordering::Greater => Err(Error::GrowSmallerNewLayout(old_layout.size(), new_layout.size()))
    }
}

/// Internal helper to grow the allocation at `ptr` by deallocating using `old_layout` and
/// reallocating using `new_layout`.
///
/// # Safety
///
/// This function doesn't check for layout validity.
/// The caller must ensure [`new_layout.size()`](Layout::size) is greater than
/// [`old_layout.size()`](Layout::size).
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(miri, track_caller)]
pub unsafe fn grow_unchecked<A: Grow + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, Error> {
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
/// The caller must ensure [`new_layout.size()`](Layout::size) is greater than
/// [`old_layout.size()`](Layout::size).
#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink_unchecked<A: Shrink + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout
) -> Result<NonNull<u8>, Error> {
    let new_ptr = tri!(do a.alloc(new_layout));

    ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
    if old_layout.size() != 0 {
        a.dealloc(ptr, old_layout);
    }

    Ok(new_ptr)
}

#[cfg_attr(miri, track_caller)]
pub unsafe fn ralloc<A: Realloc + ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, Error> {
    match old_layout.size().cmp(&new_layout.size()) {
        Ordering::Less => grow_unchecked(&a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            if new_layout.align() > old_layout.align() {
                grow_unchecked(&a, ptr, old_layout, new_layout, b)
            } else {
                Ok(ptr)
            }
        }
        Ordering::Greater => shrink_unchecked(&a, ptr, old_layout, new_layout)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Bytes {
    /// Uninitialized bytes.
    Uninitialized,
    /// Zeroed bytes.
    Zeroed
}
