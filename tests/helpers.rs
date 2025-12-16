#![allow(clippy::cast_ptr_alignment)]

use {
    core::ptr,
    memapi2::{
        Alloc,
        Dealloc,
        DefaultAlloc,
        Layout,
        data::type_props::varsized_ptr_from_parts_mut,
        error::{AlignErr, ArithErr, ArithOp, InvLayout, LayoutErr},
        helpers::{align_up, align_up_unchecked, byte_sub, checked_op, slice_ptr_from_parts_mut}
    }
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

#[test]
fn checked_op_basic_and_errors() {
    assert_eq!(checked_op(2, ArithOp::Add, 3).unwrap(), 5);
    assert_eq!(checked_op(10, ArithOp::Sub, 3).unwrap(), 7);
    assert_eq!(checked_op(4, ArithOp::Mul, 5).unwrap(), 20);
    // div by zero results in overflow err
    assert_eq!(
        checked_op(10, ArithOp::Div, 0).unwrap_err(),
        ArithErr::Overflow(10, ArithOp::Div, 0)
    );
    // pow with too-large rhs
    let big = (u32::MAX as usize) + 1;
    assert_eq!(checked_op(2, ArithOp::Pow, big).unwrap_err(), ArithErr::TooLargeRhs(big));
}

#[test]
fn align_up_and_unchecked() {
    // safe wrapper
    assert_eq!(align_up(6, 8).unwrap(), 8);
    // zero align should err
    let err = align_up(1, 0).unwrap_err();
    assert_eq!(err, InvLayout(1, 0, LayoutErr::Align(AlignErr::ZeroAlign)));

    //
    let v = unsafe { align_up_unchecked(7, 8) };
    assert_eq!(v, 8);
}

#[test]
fn dangling_nonnull_for_alignment() {
    let l = Layout::from_size_align(1, 16).unwrap();
    let p = l.dangling();
    let addr = p.as_ptr() as usize;
    assert_eq!(addr % 16, 0);
}
