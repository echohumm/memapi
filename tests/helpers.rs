#![allow(clippy::cast_ptr_alignment)]

use {
    memapi2::{
        Alloc,
        Dealloc,
        DefaultAlloc,
        Layout,
        data::type_props::varsized_ptr_from_parts_mut,
        helpers::{byte_sub, slice_ptr_from_parts_mut}
    },
    std::ptr
};

const VALUE: u64 =
    0b1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010_1010;
const BYTE: u8 = 0b1010_1010;

#[test]
fn byte_sub_stack() {
    let value = VALUE;

    let ptr = (&value as *const u64).cast::<u8>();
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
    let l = Layout::new::<u64>();
    let mem = a.alloc(l).unwrap().cast();
    unsafe {
        ptr::write(mem.as_ptr(), VALUE);
    }

    let ptr = mem.as_ptr().cast::<u8>();
    assert_eq!(unsafe { *ptr }, BYTE);
    let ptr_halfway = unsafe { ptr.add(4) };
    assert_eq!(unsafe { *ptr_halfway }, BYTE);

    let ptr_subbed = unsafe { byte_sub(ptr_halfway.cast::<u64>(), 4) };
    assert_eq!(unsafe { *ptr_subbed }, VALUE);
    assert_eq!(unsafe { *ptr_subbed.cast::<u8>() }, BYTE);

    unsafe {
        a.dealloc(mem.cast(), l);
    }
}

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
