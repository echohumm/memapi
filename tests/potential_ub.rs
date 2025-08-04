use std::ptr::NonNull;
// these tests are tests which check for potential UB, such as manually constructing a pointer with
//  metadata via transmutation.
use memapi::helpers::{nonnull_slice_from_raw_parts, nonnull_slice_len, slice_ptr_from_raw_parts};

#[test]
fn slice_ptr_from_parts_works() {
    let slice: &mut [usize] = &mut [64, 128, 256, 512];
    let ptr = slice.as_mut_ptr();
    let len = slice.len();

    let slice_ptr = slice_ptr_from_raw_parts(ptr, len);

    // check that they dereference to the same thing
    assert_eq!(unsafe { &*slice_ptr }, slice);
    // check that they have the same pointer and length
    assert_eq!(slice.as_ptr(), slice_ptr.cast::<usize>());
    assert_eq!(unsafe { slice_ptr.as_ref() }.unwrap().len(), len);

    unsafe {
        assert_eq!(
            len,
            nonnull_slice_len(nonnull_slice_from_raw_parts(
                NonNull::new_unchecked(ptr),
                len
            ))
        );
    }

    for (i, elem) in slice.iter().enumerate() {
        // check that the values are all the same
        assert_eq!(*elem, unsafe { (&*slice_ptr)[i] });

        // manually check that the values are the same
        assert_eq!(unsafe { (&*slice_ptr)[i] }, 64usize << i);
    }
}
