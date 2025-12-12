#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]

use {
    core::{alloc::Layout, ptr},
    memapi2::{traits::*, DefaultAlloc, error::AllocError}
};

#[test]
fn test_alloc_and_dealloc() {
    // TODO: tests for the vs_or_s_p fns. probably put checks in build.rs too, the whole system is
    //  built on assumptions and held together with tape.
    // match varsized_or_sized_pointer_from_raw_parts::<u8>(null_mut(), 8) {
    //     Ptr::Sized(p) => println!("correct"),
    //     Ptr::Unsized(p) => println!("incorrect"),
    // }

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
    let old = Layout::from_size_align(8, 1).unwrap();
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
