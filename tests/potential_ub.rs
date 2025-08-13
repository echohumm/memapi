//#![allow(clippy::undocumented_unsafe_blocks)]
// these tests are tests which check for potential UB, such as manually constructing a pointer with
//  metadata via transmutation.
use core::ptr::NonNull;
use memapi::helpers::{nonnull_slice_from_raw_parts, nonnull_slice_len, slice_ptr_from_raw_parts};

#[test]
fn slice_pointer_from_raw_parts_works() {
    match sp_frp_inner() {
        // 0 == success, no ub
        0 => (),
        1 => panic!("slice_ptr_from_raw_parts() test 1 failed: result doesn't dereference properly"),
        2 => panic!("slice_ptr_from_raw_parts() test 2 failed: result doesn't have the same pointer"),
        3 => panic!("slice_ptr_from_raw_parts() test 3 failed: result doesn't have the same length"),
        4 => panic!("slice_ptr_from_raw_parts() test 4 failed: result as nonnull doesn't have the same length"),
        5 => panic!("slice_ptr_from_raw_parts() test 5 failed: result doesn't have the same values"),
        6 => panic!("slice_ptr_from_raw_parts() test 6 failed: result doesn't have the correct values"),
        // SAFETY: sp_frp_inner returns at most 6.
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}

fn sp_frp_inner() -> usize {
    let i = 4;

    let mut data: Vec<usize> = (0..i).map(|j| 64 << j).collect();
    let slice: &mut [usize] = &mut data;

    let ptr = slice.as_mut_ptr();
    let len = slice.len();

    let slice_ptr = slice_ptr_from_raw_parts(ptr, len);

    // check that they dereference to the same thing
    if unsafe { &*slice_ptr } != slice {
        return 1;
    }
    // check that they have the same pointer and length
    if slice.as_ptr() != slice_ptr.cast::<usize>() {
        return 2;
    }
    if unsafe { slice_ptr.as_ref() }.unwrap().len() != len {
        return 3;
    }

    unsafe {
        if len
            != nonnull_slice_len(nonnull_slice_from_raw_parts(
                NonNull::new_unchecked(ptr),
                len,
            ))
        {
            return 4;
        }
    }

    for (i, elem) in slice.iter().enumerate() {
        // check that the values are all the same
        if *elem != unsafe { (&*slice_ptr)[i] } {
            return 5;
        }

        // manually check that the values are the same
        if unsafe { (&*slice_ptr)[i] } != 64usize << i {
            return 6;
        }
    }

    0
}
