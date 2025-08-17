// miri is incompatible with malloc_defaultalloc
#![cfg_attr(feature = "malloc_defaultalloc", cfg(not(miri)))]
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use core::ptr;
use memapi::{type_props::SizedProps, Alloc, AllocExt, DefaultAlloc, Layout};

#[test]
#[allow(clippy::cast_possible_truncation)]
fn test_alloc_filled() {
    let allocator = DefaultAlloc;
    let layout = Layout::from_size_align(8, 1).unwrap();
    // Filled
    let ptr_filled = allocator.falloc(layout, 0x5A).unwrap();
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr_filled.as_ptr().add(i), 0x5A);
        }
        allocator.dealloc(ptr_filled, layout);
    }
}

#[test]
#[allow(clippy::cast_possible_truncation)]
fn test_grow_and_variants() {
    let allocator = DefaultAlloc;
    let old = Layout::from_size_align(4, 1).unwrap();
    let new = Layout::from_size_align(8, 1).unwrap();
    // Prepare initial block with values 1,2,3,4
    let ptr = allocator.alloc(old).unwrap();
    unsafe {
        for i in 0..old.size() {
            *ptr.as_ptr().add(i) = (i + 1) as u8;
        }
    }
    // grow without a pattern: new bytes undefined but old preserved
    let grown = unsafe { allocator.grow(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), (i + 1) as u8);
        }
        allocator.dealloc(grown, new);
    }

    // grow_zeroed: new tail zeros
    let ptr2 = allocator.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(ptr2.as_ptr(), 0xFF, old.size());
    }
    let gz = unsafe { allocator.zgrow(ptr2, old, new).unwrap() };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*gz.as_ptr().add(i), 0xFF);
        }
        for i in old.size()..new.size() {
            assert_eq!(*gz.as_ptr().add(i), 0);
        }
        allocator.dealloc(gz, new);
    }

    // grow_filled
    let ptr3 = allocator.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(ptr3.as_ptr(), 0xAA, old.size());
    }
    let gf = unsafe { allocator.fgrow(ptr3, old, new, 0xBB).unwrap() };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*gf.as_ptr().add(i), 0xAA);
        }
        for i in old.size()..new.size() {
            assert_eq!(*gf.as_ptr().add(i), 0xBB);
        }
        allocator.dealloc(gf, new);
    }
}
#[test]
fn test_realloc_variants() {
    let allocator = DefaultAlloc;
    let old = Layout::from_size_align(4, 1).unwrap();
    let new = Layout::from_size_align(2, 1).unwrap();
    let ptr = allocator.falloc(old, 0xDD).unwrap();
    // realloc shrink
    let rs = unsafe { allocator.realloc(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*rs.as_ptr().add(i), 0xDD);
        }
        allocator.dealloc(rs, new);
    }

    // realloc grow
    let ptr2 = allocator.zalloc(old).unwrap();
    let rg = unsafe {
        allocator
            .rezalloc(ptr2, old, Layout::from_size_align(6, 1).unwrap())
            .unwrap()
    };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*rg.as_ptr().add(i), 0);
        }
        for i in old.size()..6 {
            assert_eq!(*rg.as_ptr().add(i), 0);
        }
        allocator.dealloc(rg, Layout::from_size_align(6, 1).unwrap());
    }
}
