//#![allow(clippy::undocumented_unsafe_blocks)]
use core::{alloc::Layout, ptr};
use memapi::{
    error::AllocError,
    unstable_util::{layout_padding_for, pad_layout_to_align, repeat_layout, repeat_layout_packed},
    Alloc, DefaultAlloc,
};

// TODO: break up big tests into smaller, more generalized ones

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
    let ptr = allocator.alloc_zeroed(layout).expect("alloc_zeroed failed");
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
    assert_eq!(
        err,
        AllocError::ShrinkBiggerNewLayout(new.size(), old.size())
    );

    // error: grow to a smaller size
    let err2 = unsafe { allocator.grow(shr, old, new).unwrap_err() };
    assert_eq!(
        err2,
        AllocError::GrowSmallerNewLayout(old.size(), new.size())
    );

    unsafe {
        allocator.dealloc(shr, new);
    }
}

#[test]
fn test_pad_layout_functions() {
    let layout = Layout::from_size_align(10, 4).unwrap();
    let padding_size = layout_padding_for(layout, 4);
    assert_eq!(padding_size, 2);

    let aligned_layout = pad_layout_to_align(layout);
    assert_eq!(aligned_layout.align(), 4);
    assert_eq!(aligned_layout.size(), 12);
}

#[test]
fn test_repeat_layout_variants() {
    let layout = Layout::from_size_align(4, 4).unwrap();
    let (rep, count) = repeat_layout(layout, 3).unwrap();
    assert_eq!(count, 4);
    assert_eq!(rep.size(), 4 * 3);
    assert_eq!(rep.align(), 4);

    let rep_packed = repeat_layout_packed(layout, 5).unwrap();
    assert_eq!(rep_packed.size(), 4 * 5);
    assert_eq!(rep_packed.align(), 4);
}
