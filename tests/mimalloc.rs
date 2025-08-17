#![allow(clippy::undocumented_unsafe_blocks)]
#![cfg(not(miri))]
use core::ptr;
use memapi::{external::ffi::mim::mi_usable_size, external::mimalloc::MiMalloc, Alloc, Layout};

#[test]
fn alloc_and_dealloc_basic() {
    let alloc = MiMalloc;
    let layout = Layout::from_size_align(16, 8).unwrap();
    let ptr = alloc.alloc(layout).unwrap();
    unsafe {
        alloc.dealloc(ptr, layout);
    }
}

#[test]
fn alloc_zeroed_is_really_zeroed() {
    let alloc = MiMalloc;
    let size = 64;
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = alloc.zalloc(layout).unwrap();
    unsafe {
        let slice = core::slice::from_raw_parts(ptr.as_ptr(), size);
        assert!(slice.iter().all(|&b| b == 0), "all bytes must be zero");
        alloc.dealloc(ptr, layout);
    }
}

#[test]
fn usable_size_at_least_requested() {
    let alloc = MiMalloc;
    let size = 100;
    let layout = Layout::from_size_align(size, 16).unwrap();
    let ptr = alloc.alloc(layout).unwrap();
    unsafe {
        let actual = mi_usable_size(ptr.as_ptr().cast());
        assert!(
            actual >= size,
            "usable_size {} should be >= requested {}",
            actual,
            size
        );
        alloc.dealloc(ptr, layout);
    }
}

#[test]
fn realloc_preserves_initial_contents() {
    let alloc = MiMalloc;
    let count = 8;
    let elem_layout = Layout::array::<u32>(count).unwrap();
    unsafe {
        // allocate and fill with a pattern
        let ptr0 = alloc.alloc(elem_layout).unwrap().cast::<u32>();
        for i in 0..count {
            #[allow(clippy::cast_possible_truncation)]
            ptr::write(ptr0.as_ptr().add(i), (i as u32).wrapping_mul(3) + 1);
        }
        // grow to twice the byte size
        let new_bytes = elem_layout.size() * 2;
        let new_layout = Layout::from_size_align(new_bytes, elem_layout.align()).unwrap();
        let ptr1 = alloc
            .realloc(ptr0.cast(), elem_layout, new_layout)
            .unwrap()
            .cast::<u32>();
        // verify old data
        #[allow(clippy::cast_possible_truncation)]
        for i in 0..count {
            let v = ptr::read(ptr1.as_ptr().add(i));
            assert_eq!(v, (i as u32).wrapping_mul(3) + 1);
        }
        alloc.dealloc(ptr1.cast(), new_layout);
    }
}

#[test]
fn allocations_are_properly_aligned() {
    let alloc = MiMalloc;
    // test a variety of alignments
    for &align in &[1, 2, 8, 16, 32, 64] {
        let size = 24;
        let layout = Layout::from_size_align(size, align).unwrap();
        let ptr = alloc.alloc(layout).unwrap();
        let addr = ptr.as_ptr() as usize;
        assert_eq!(
            addr % align,
            0,
            "pointer {:#x} must be aligned to {} bytes",
            addr,
            align
        );
        unsafe {
            alloc.dealloc(ptr, layout);
        }
    }
}

#[cfg(feature = "mimalloc_err_reporting")]
#[test]
fn error_reporting_works() {
    use memapi::{
        error::{AllocError, Cause},
        type_props::{usize_bit, USIZE_MAX_NO_HIGH_BIT},
    };

    let alloc = MiMalloc;

    memapi::external::mimalloc::init_error_handler();

    // creation will succeed, but this amount of memory is far too large for anything to allocate.
    let layout = unsafe { Layout::from_size_align_unchecked(USIZE_MAX_NO_HIGH_BIT, 1) };

    let err = alloc.alloc(layout).expect_err("allocation should fail");

    match err {
        AllocError::AllocFailed(_, ref c) => match c {
            Cause::Unknown => panic!("unexpected cause: {}", c),
            Cause::OutOfMemory => panic!("how..?"),
            #[cfg(feature = "fallible_dealloc")]
            Cause::InvalidBlockStatus(_) => panic!("what"),
            Cause::OSErr(e) => println!("{:?}", e),
        },
        _ => panic!("unexpected error: {}", err),
    }

    let layout2 = unsafe { Layout::from_size_align_unchecked(1, usize_bit(1)) };

    let err2 = alloc.alloc(layout2).expect_err("allocation should fail");

    match err2 {
        AllocError::AllocFailed(_, ref c) => match c {
            Cause::Unknown => panic!("unexpected cause: {}", c),
            Cause::OutOfMemory => panic!("how..?"),
            #[cfg(feature = "fallible_dealloc")]
            Cause::InvalidBlockStatus(_) => panic!("what"),
            Cause::OSErr(e) => println!("{:?}", e),
        },
        _ => panic!("unexpected error: {}", err),
    }
}
