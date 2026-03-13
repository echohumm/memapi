#![cfg(any(not(feature = "no_alloc"), feature = "std"))]
#![allow(clippy::cast_ptr_alignment)]

use {
    ::core::ptr::{self, NonNull},
    memapi2::{
        helpers::{
            align_up,
            is_multiple_of,
            nonnull_slice_from_parts,
            nonnull_slice_len,
            slice_ptr_from_parts_mut
        },
        layout::Layout,
        traits::data::type_props::varsized_ptr_from_parts_mut
    }
};

#[test]
fn slice_ptr_from_parts_stack_roundtrip() {
    let mut arr = [1u32, 2, 3, 4];
    let raw_slice = slice_ptr_from_parts_mut(arr.as_mut_ptr(), arr.len());

    {
        let s: &mut [u32] = unsafe { &mut *raw_slice };
        assert_eq!(s, &mut [1, 2, 3, 4]);
    }
    assert!(ptr::eq(&arr, raw_slice as *const _));
}

#[test]
fn varsized_ptr_from_parts_for_slices() {
    let mut arr = [10u16, 20, 30];
    let raw_slice: *mut [u16] =
        varsized_ptr_from_parts_mut(arr.as_mut_ptr().cast::<u8>(), arr.len());

    {
        let s: &mut [u16] = unsafe { &mut *raw_slice };
        assert_eq!(s, &mut [10, 20, 30]);
    }
    assert!(ptr::eq(&arr, raw_slice as *const _));
}

#[test]
fn align_up_basic() {
    assert_eq!(unsafe { align_up(7, 8) }, 8);
    assert_eq!(unsafe { align_up(8, 16) }, 16);
    assert_eq!(unsafe { align_up(23, 8) }, 24);
}

#[rustversion::since(1.57)]
#[test]
#[should_panic = "unsafe precondition(s) violated: `align_up` requires that `align` is a non-zero \
                  power of two and that `v + (align - 1)` does not overflow."]
fn align_up_zero_align() {
    let _ = unsafe { align_up(7, 0) };
}

#[rustversion::since(1.57)]
#[test]
#[should_panic = "unsafe precondition(s) violated: `align_up` requires that `align` is a non-zero \
                  power of two and that `v + (align - 1)` does not overflow."]
fn align_up_nonpow2() {
    let _ = unsafe { align_up(7, 3) };
}

#[rustversion::since(1.57)]
#[test]
#[should_panic = "unsafe precondition(s) violated: `align_up` requires that `align` is a non-zero \
                  power of two and that `v + (align - 1)` does not overflow."]
fn align_up_overflow() {
    // usize limit is 18_446_744_073_709_551_615, that + (a - 1) where a > 1 will overflow
    let _ = unsafe { align_up(18_446_744_073_709_551_615, 2) };
}

#[test]
fn dangling_nonnull_for_alignment() {
    let l = Layout::from_size_align(1, 16).unwrap();
    let p = l.dangling();
    let addr = p.as_ptr() as usize;
    assert_eq!(addr % 16, 0);
}

#[test]
fn is_multiple_of_zero_rhs() {
    assert!(is_multiple_of(0, 0));
    assert!(!is_multiple_of(1, 0));
}

#[test]
fn nonnull_slice_from_parts_roundtrip() {
    let mut arr = [1u8, 2, 3];
    let ptr = unsafe { NonNull::new_unchecked(arr.as_mut_ptr()) };
    let slice_ptr = nonnull_slice_from_parts(ptr, arr.len());
    let len = unsafe { nonnull_slice_len(slice_ptr) };

    assert_eq!(len, arr.len());
    assert_eq!(unsafe { slice_ptr.as_ref() }, &arr);
}
