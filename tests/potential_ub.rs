// these tests are tests which check for potential UB, such as manually constructing a pointer with
//  metadata via transmutation.
use memapi::helpers::slice_ptr_from_raw_parts;

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
    assert_eq!(slice_ptr.len(), len);

    for (i, elem) in slice.iter().enumerate() {
        // check that the values are all the same
        assert_eq!(*elem, unsafe { (&*slice_ptr)[i] });

        // manually check that the values are the same
        assert_eq!(unsafe { (&*slice_ptr)[i] }, 64usize << i);
    }
}
