use {
    core::ptr::NonNull,
    memapi2::{AllocTemp, Layout, c_alloc::StackAlloc, error::Error}
};

#[test]
fn stack_alloc() {
    unsafe {
        StackAlloc.alloc_temp(
            Layout::from_size_align(8, 8).unwrap(),
            |ptr: Result<NonNull<u8>, Error>| {
                let ptr = ptr.unwrap();
                assert_eq!(ptr.as_ptr() as usize % 8, 0);
            }
        );
    }
}
