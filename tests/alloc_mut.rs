#![cfg(not(feature = "no_alloc"))]
extern crate alloc;

use {
    ::core::{ptr, ptr::NonNull},
    memapi2::{
        DefaultAlloc,
        error::Error,
        layout::Layout,
        traits::{
            AllocDescriptor,
            AllocFeatures,
            alloc_mut::{AllocMut, DeallocMut, ReallocMut}
        }
    }
};

/// Test allocator that only implements AllocMut and DeallocMut.
#[derive(Debug, Clone, Copy, Default)]
struct MutOnlyAlloc;

impl AllocDescriptor for MutOnlyAlloc {
    type Error = Error;

    const FEATURES: AllocFeatures = AllocFeatures::DEALLOC;
}

impl AllocMut for MutOnlyAlloc {
    #[inline]
    fn alloc_mut(&mut self, layout: Layout) -> Result<NonNull<u8>, Error> {
        DefaultAlloc.alloc_mut(layout)
    }
}

impl DeallocMut for MutOnlyAlloc {
    #[inline]
    unsafe fn try_dealloc_mut(&mut self, ptr: NonNull<u8>, layout: Layout) -> Result<(), Error> {
        DefaultAlloc.try_dealloc_mut(ptr, layout)
    }
}
impl ReallocMut for MutOnlyAlloc {}

#[test]
fn test_alloc_and_dealloc() {
    let mut allocator = MutOnlyAlloc;
    let layout = Layout::from_size_align(16, 8).unwrap();
    // Allocate
    let ptr = allocator.alloc_mut(layout).expect("alloc failed");
    // Write and read
    unsafe {
        ptr::write_bytes(ptr.as_ptr(), 0xAB, layout.size());
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0xAB);
        }
        allocator.dealloc_mut(ptr, layout);
    }
}

#[test]
fn test_alloc_zeroed() {
    let mut allocator = MutOnlyAlloc;
    let layout = Layout::from_size_align(32, 8).unwrap();
    let ptr = allocator.zalloc_mut(layout).expect("alloc_zeroed failed");
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0, "failed on byte {}", i);
        }
        allocator.dealloc_mut(ptr, layout);
    }
}

#[test]
fn grow_preserves_prefix() {
    let mut a = MutOnlyAlloc;
    let old = Layout::from_size_align(8, 8).unwrap();
    let new = Layout::from_size_align(16, 8).unwrap();

    let p = a.alloc_mut(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0x11, old.size());
    }

    let grown = unsafe { a.realloc_mut(p, old, new).unwrap() };
    // first 8 bytes preserved
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), 0x11);
        }
        a.dealloc_mut(grown, new);
    }
}

#[test]
fn rezalloc_zeros_new_region() {
    let mut a = MutOnlyAlloc;
    let old = Layout::from_size_align(8, 8).unwrap();
    let new = Layout::from_size_align(16, 8).unwrap();

    let p = a.alloc_mut(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0x22, old.size());
    }

    let grown = unsafe { a.rezalloc_mut(p, old, new).unwrap() };
    unsafe {
        // original region preserved
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), 0x22);
        }
        // new region zeroed
        for i in old.size()..new.size() {
            assert_eq!(*grown.as_ptr().add(i), 0);
        }
        a.dealloc_mut(grown, new);
    }
}

#[test]
fn shrink_preserves_prefix() {
    let mut a = MutOnlyAlloc;
    let old = Layout::from_size_align(16, 8).unwrap();
    let new = Layout::from_size_align(8, 8).unwrap();

    let p = a.alloc_mut(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0xAB, old.size());
    }

    let shr = unsafe { a.realloc_mut(p, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*shr.as_ptr().add(i), 0xAB);
        }
        a.dealloc_mut(shr, new);
    }
}
