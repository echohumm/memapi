// miri is incompatible with malloc_defaultalloc
#![cfg_attr(feature = "malloc_defaultalloc", cfg(not(miri)))]
#![cfg(any(not(feature = "no_alloc"), feature = "malloc_defaultalloc"))]
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use {
    core::ptr,
    memapi::{Alloc, DefaultAlloc, Layout, error::AllocError, data::type_props::SizedProps}
};

#[test]
fn test_alloc_and_dealloc() {
    let allocator = DefaultAlloc;
    let layout = Layout::from_size_align(16, 8).unwrap();
    // Allocate
    let ptr = allocator.alloc(layout).expect("alloc failed");
    // Write and read
    unsafe {
        ptr::write_bytes(ptr.as_ptr(), 0xAB, layout.size());
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0xAB);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
fn test_alloc_zeroed() {
    let allocator = DefaultAlloc;
    let layout = Layout::from_size_align(32, 8).unwrap();
    let ptr = allocator.zalloc(layout).expect("alloc_zeroed failed");
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
fn test_shrink_and_error_cases() {
    let allocator = DefaultAlloc;
    let old = Layout::from_size_align(
        8,
        // alignment must be a power of two AND a multiple of *void's size for malloc.
        //  usize::SZ = *void's size
        if cfg!(feature = "malloc_defaultalloc") { usize::SZ } else { 1 }
    )
    .unwrap();
    // 1 is fine here though because we already satisfy the alignment, and
    //  1 < MAXIMUM_GUARANTEED_ALIGNMENT
    let new = Layout::from_size_align(4, 1).unwrap();
    let ptr = allocator.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(ptr.as_ptr(), 0xCC, old.size());
    }
    let shr = unsafe { allocator.shrink(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*shr.as_ptr().add(i), 0xCC);
        }
    }

    // error: shrink to a larger size
    let err = unsafe { allocator.shrink(shr, new, old).unwrap_err() };
    assert_eq!(err, AllocError::ShrinkLargerNewLayout(new.size(), old.size()));

    // error: grow to a smaller size
    let err2 = unsafe { allocator.grow(shr, old, new).unwrap_err() };
    assert_eq!(err2, AllocError::GrowSmallerNewLayout(old.size(), new.size()));

    unsafe {
        allocator.dealloc(shr, new);
    }
}
