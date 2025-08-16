// miri is incompatible with malloc_defaultalloc
#![cfg(any(not(miri), not(feature = "malloc_defaultalloc")))]
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use core::ptr;
use memapi::{Alloc, AllocSlice, DefaultAlloc, Layout};

#[test]
fn test_alloc_init_and_default_slice() {
    let allocator = DefaultAlloc;
    let len = 3;
    // alloc_init_slice
    let sptr = unsafe {
        allocator.isalloc::<u32, _>(len, |p, init| {
            let p = p.cast::<u32>();
            for i in 0..len {
                ptr::write(p.as_ptr().add(i), 5);
                *init += 1;
            }
        })
    }
    .unwrap();
    let slice_ref: &[u32] = unsafe { sptr.as_ref() };
    assert_eq!(slice_ref, &[5; 3]);
    unsafe {
        allocator.dealloc(sptr.cast(), Layout::array::<u32>(len).unwrap());
    }

    // alloc_default_slice
    let dptr = allocator.salloc_def::<u32>(len).unwrap();
    let dslice: &[u32] = unsafe { dptr.as_ref() };
    assert_eq!(dslice, &[0; 3]);
    unsafe {
        allocator.dealloc(dptr.cast(), Layout::array::<u32>(len).unwrap());
    }
}
