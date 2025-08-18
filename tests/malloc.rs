#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
#![cfg(not(miri))]
#![cfg(unix)]
use {
    core::{
        ptr::{self, NonNull},
        slice
    },
    memapi::{
        Alloc,
        Layout,
        external::{ffi::libc::malloc_usable_size, malloc::Malloc},
        type_props::SizedProps
    }
};

#[test]
fn alloc_and_dealloc_basic() {
    println!("alloc_and_dealloc_basic");
    let alloc = Malloc;
    let layout = Layout::from_size_align(64, 8).unwrap();

    unsafe {
        let ptr = alloc.alloc(layout).unwrap();
        // we can write into the block
        ptr::write_bytes(ptr.as_ptr(), 0xAB, layout.size());
        alloc.dealloc(ptr, layout);
    }
}

#[test]
fn alloc_zeroed_is_really_zeroed() {
    println!("alloc_zeroed_is_really_zeroed");
    let alloc = Malloc;
    let size = 128;
    let layout = Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = alloc.zalloc(layout).unwrap();
        // treat as byte slice
        let buf = slice::from_raw_parts(ptr.as_ptr(), size);
        assert!(buf.iter().all(|&b| b == 0), "alloc_zeroed must produce all-zero bytes");
        alloc.dealloc(ptr, layout);
    }
}

#[test]
fn usable_size_at_least_requested() {
    let alloc = Malloc;
    let size = 100;
    let layout = Layout::from_size_align(size, 16).unwrap();

    unsafe {
        let ptr = alloc.alloc(layout).unwrap();
        let usable = malloc_usable_size(ptr.as_ptr().cast());
        assert!(usable >= size, "usable_size {} should be >= requested {}", usable, size);
        alloc.dealloc(ptr, layout);
    }
}

#[test]
#[allow(clippy::cast_possible_truncation)]
fn realloc_preserves_initial_contents() {
    println!("realloc_preserves_initial_contents");
    let alloc = Malloc;
    let old_count = 4;
    let old_layout = Layout::array::<u32>(old_count).unwrap().align_to(usize::SZ).unwrap();

    unsafe {
        // allocate and write a pattern
        let ptr = alloc.alloc(old_layout).unwrap().cast::<u32>();
        for i in 0..old_count {
            ptr::write(ptr.as_ptr().add(i), i as u32 + 1);
        }

        // grow to twice as many elements
        let new_size = old_count * 2 * u32::SZ;
        let new_layout = Layout::from_size_align_unchecked(new_size, u32::ALN);
        let new_ptr: NonNull<u32> =
            alloc.realloc(ptr.cast(), old_layout, new_layout).unwrap().cast();

        // original data should be intact
        for i in 0..old_count {
            let v: u32 = ptr::read(new_ptr.as_ptr().add(i));
            assert_eq!(v, i as u32 + 1);
        }

        // cleanup
        let new_layout = Layout::from_size_align(new_size, old_layout.align()).unwrap();
        alloc.dealloc(new_ptr.cast(), new_layout);
    }
}

#[cfg(feature = "os_err_reporting")]
#[test]
fn error_reporting_works() {
    use memapi::{
        error::{AllocError, Cause},
        type_props::{USIZE_MAX_NO_HIGH_BIT, usize_bit}
    };

    let alloc = Malloc;

    // we have to lower this for malloc, because of its rounding up of the alignment which size is
    //  then rounded up to
    let layout = unsafe { Layout::from_size_align_unchecked(USIZE_MAX_NO_HIGH_BIT - 7, 1) };

    let err = alloc.alloc(layout).expect_err("allocation should fail");

    match err {
        AllocError::AllocFailed(_, ref c) => match c {
            Cause::Unknown => panic!("unexpected cause: {}", c),
            Cause::OutOfMemory => panic!("how..?"),
            #[cfg(feature = "fallible_dealloc")]
            Cause::InvalidBlockStatus(_) => panic!("what"),
            Cause::OSErr(e) => println!("{:?}", e)
        },
        _ => panic!("unexpected error: {}", err)
    }

    let layout2 = unsafe { Layout::from_size_align_unchecked(1, usize_bit(1)) };

    let err2 = alloc.alloc(layout2).expect_err("allocation should fail");

    match err2 {
        AllocError::AllocFailed(_, ref c) => match c {
            Cause::Unknown => panic!("unexpected cause: {}", c),
            Cause::OutOfMemory => panic!("how..?"),
            #[cfg(feature = "fallible_dealloc")]
            Cause::InvalidBlockStatus(_) => panic!("what"),
            Cause::OSErr(e) => println!("{:?}", e)
        },
        _ => panic!("unexpected error: {}", err)
    }
}
