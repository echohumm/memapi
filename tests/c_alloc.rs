#![cfg(feature = "c_alloc")]

use {
    memapi2::{Alloc, Dealloc, Grow, Layout, Shrink, c_alloc::CAlloc, error::Error},
    std::ptr
};
use memapi2::data::type_props::SizedProps;

#[test]
fn test_alloc_and_dealloc() {
    let allocator = CAlloc;
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
    let allocator = CAlloc;
    let layout = Layout::from_size_align(32, 8).unwrap();
    let ptr = allocator.zalloc(layout).expect("alloc_zeroed failed");
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0, "failed on byte {}", i);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
fn test_shrink_and_error_cases() {
    let allocator = CAlloc;
    let old = Layout::from_size_align(32, usize::SZ).unwrap();
    // 1 is fine here though because we already satisfy the alignment, and
    //  1 < MAXIMUM_GUARANTEED_ALIGNMENT
    let new = Layout::from_size_align(16, usize::SZ).unwrap();
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
    assert_eq!(err, Error::ShrinkLargerNewLayout(new.size(), old.size()));

    // error: grow to a smaller size
    let err2 = unsafe { allocator.grow(shr, old, new).unwrap_err() };
    assert_eq!(err2, Error::GrowSmallerNewLayout(old.size(), new.size()));

    unsafe {
        allocator.dealloc(shr, new);
    }
}

#[test]
fn grow_preserves_prefix() {
    let a = CAlloc;
    let old = Layout::from_size_align(8, 8).unwrap();
    let new = Layout::from_size_align(16, 8).unwrap();

    let p = a.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0x11, old.size());
    }

    let grown = unsafe { a.grow(p, old, new).unwrap() };
    // first 8 bytes preserved
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), 0x11);
        }
        a.dealloc(grown, new);
    }
}

#[test]
fn zgrow_zeros_new_region() {
    let a = CAlloc;
    let old = Layout::from_size_align(8, 8).unwrap();
    let new = Layout::from_size_align(16, 8).unwrap();

    let p = a.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0x22, old.size());
    }

    let grown = unsafe { a.zgrow(p, old, new).unwrap() };
    unsafe {
        // original region preserved
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), 0x22);
        }
        // new region zeroed
        for i in old.size()..new.size() {
            assert_eq!(*grown.as_ptr().add(i), 0);
        }
        a.dealloc(grown, new);
    }
}

#[test]
fn shrink_preserves_prefix() {
    let a = CAlloc;
    let old = Layout::from_size_align(16, 8).unwrap();
    let new = Layout::from_size_align(8, 8).unwrap();

    let p = a.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0xAB, old.size());
    }

    let shr = unsafe { a.shrink(p, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*shr.as_ptr().add(i), 0xAB);
        }
        a.dealloc(shr, new);
    }
}
