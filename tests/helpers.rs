// provenance is annoying. this crate definitely has more issues with it than i am aware of
#![cfg(not(miri))]
#![allow(clippy::cast_ptr_alignment)]
use {
    memapi2::{Alloc, DefaultAlloc, helpers::byte_sub},
    std::alloc::Layout
};

const VALUE: u64 =
    0b1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010;
const BYTE: u8 = 0b1010_1010;

#[test]
fn byte_sub_stack() {
    let ptr = (&VALUE as *const u64).cast::<u8>();
    assert_eq!(unsafe { *ptr }, BYTE);
    let ptr_halfway = unsafe { ptr.add(4) };
    assert_eq!(unsafe { *ptr_halfway }, BYTE);

    let ptr_subbed = unsafe { byte_sub(ptr_halfway.cast::<u64>(), 4) };
    assert_eq!(unsafe { *ptr_subbed }, VALUE);
    assert_eq!(unsafe { *ptr_subbed.cast::<u8>() }, BYTE);
}

#[test]
fn byte_sub_heap() {
    let a = DefaultAlloc;
    let mem = a.alloc(Layout::new::<u64>()).unwrap().cast();
    unsafe {
        mem.write(VALUE);
    }

    let ptr = mem.as_ptr().cast::<u8>();
    assert_eq!(unsafe { *ptr }, BYTE);
    let ptr_halfway = unsafe { ptr.add(4) };
    assert_eq!(unsafe { *ptr_halfway }, BYTE);

    let ptr_subbed = unsafe { byte_sub(ptr_halfway.cast::<u64>(), 4) };
    assert_eq!(unsafe { *ptr_subbed }, VALUE);
    assert_eq!(unsafe { *ptr_subbed.cast::<u8>() }, BYTE);
}
