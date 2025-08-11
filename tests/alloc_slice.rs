//#![allow(clippy::undocumented_unsafe_blocks)]
use core::{alloc::Layout, ptr};
use memapi::{Alloc, AllocSlice, DefaultAlloc};

#[test]
fn test_alloc_init_and_default_slice() {
    let allocator = DefaultAlloc;
    let len = 3;
    // alloc_init_slice
    let sptr = unsafe {
        allocator.alloc_slice_init::<u32, _>(
            |p, init| {
                let p = p.cast::<u32>();
                for i in 0..len {
                    ptr::write(p.as_ptr().add(i), 5);
                    *init += 1;
                }
            },
            len,
        )
    }
    .unwrap();
    let slice_ref: &[u32] = unsafe { sptr.as_ref() };
    assert_eq!(slice_ref, &[5; 3]);
    unsafe {
        allocator.dealloc(sptr.cast(), Layout::array::<u32>(len).unwrap());
    }

    // alloc_default_slice
    let dptr = allocator.alloc_slice_default::<u32>(len).unwrap();
    let dslice: &[u32] = unsafe { dptr.as_ref() };
    assert_eq!(dslice, &[0; 3]);
    unsafe {
        allocator.dealloc(dptr.cast(), Layout::array::<u32>(len).unwrap());
    }
}
