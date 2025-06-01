use core::alloc::Layout;
use memapi::unstable_util::{
    pad_layout_for, pad_layout_to_align, repeat_layout, repeat_layout_packed,
};
use memapi::{Alloc, AllocError, DefaultAlloc};

#[test]
fn test_alloc_and_dealloc() {
    let allocator = DefaultAlloc;
    let layout = Layout::from_size_align(16, 8).unwrap();
    // Allocate
    let ptr = allocator.alloc(layout).expect("alloc failed");
    // Write and read
    unsafe {
        ptr.as_ptr().write_bytes(0xAB, layout.size());
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0xAB);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
fn test_alloc_zeroed() {
    let allocator = DefaultAlloc;
    let layout = Layout::from_size_align(32, 8).unwrap();
    let ptr = allocator.alloc_zeroed(layout).expect("alloc_zeroed failed");
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
#[allow(clippy::cast_possible_truncation)]
fn test_alloc_filled_and_patterned() {
    let allocator = DefaultAlloc;
    let layout = Layout::from_size_align(8, 1).unwrap();
    // Filled
    let ptr_filled = allocator.alloc_filled(layout, 0x5A).unwrap();
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr_filled.as_ptr().add(i), 0x5A);
        }
        allocator.dealloc(ptr_filled, layout);
    }

    // Patterned: pattern = i
    let ptr_pat = allocator
        .alloc_patterned(layout, |i| (i as u8) * 2)
        .unwrap();
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr_pat.as_ptr().add(i), (i as u8) * 2);
        }
        allocator.dealloc(ptr_pat, layout);
    }
}

#[test]
#[allow(clippy::cast_possible_truncation)]
fn test_grow_and_variants() {
    let allocator = DefaultAlloc;
    let old = Layout::from_size_align(4, 1).unwrap();
    let new = Layout::from_size_align(8, 1).unwrap();
    // Prepare initial block with values 1,2,3,4
    let ptr = allocator.alloc(old).unwrap();
    unsafe {
        for i in 0..old.size() {
            *ptr.as_ptr().add(i) = (i + 1) as u8;
        }
    }
    // grow without a pattern: new bytes undefined but old preserved
    let grown = unsafe { allocator.grow(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), (i + 1) as u8);
        }
        allocator.dealloc(grown, new);
    }

    // grow_zeroed: new tail zeros
    let ptr2 = allocator.alloc(old).unwrap();
    unsafe {
        ptr2.as_ptr().write_bytes(0xFF, old.size());
    }
    let gz = unsafe { allocator.grow_zeroed(ptr2, old, new).unwrap() };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*gz.as_ptr().add(i), 0xFF);
        }
        for i in old.size()..new.size() {
            assert_eq!(*gz.as_ptr().add(i), 0);
        }
        allocator.dealloc(gz, new);
    }

    // grow_filled
    let ptr3 = allocator.alloc(old).unwrap();
    unsafe {
        ptr3.as_ptr().write_bytes(0xAA, old.size());
    }
    let gf = allocator.grow_filled(ptr3, old, new, 0xBB).unwrap();
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*gf.as_ptr().add(i), 0xAA);
        }
        for i in old.size()..new.size() {
            assert_eq!(*gf.as_ptr().add(i), 0xBB);
        }
        allocator.dealloc(gf, new);
    }

    // grow_patterned
    let ptr4 = allocator.alloc(old).unwrap();
    unsafe {
        ptr4.as_ptr().write_bytes(0x00, old.size());
    }
    let gp = unsafe {
        allocator
            .grow_patterned(ptr4, old, new, |i| (i as u8) + 1)
            .unwrap()
    };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*gp.as_ptr().add(i), 0);
        }
        for i in old.size()..new.size() {
            assert_eq!(*gp.as_ptr().add(i), (i as u8) + 1);
        }
        allocator.dealloc(gp, new);
    }
}

#[test]
fn test_shrink_and_error_cases() {
    let allocator = DefaultAlloc;
    let old = Layout::from_size_align(8, 1).unwrap();
    let new = Layout::from_size_align(4, 1).unwrap();
    let ptr = allocator.alloc(old).unwrap();
    unsafe {
        ptr.as_ptr().write_bytes(0xCC, old.size());
    }
    let shr = unsafe { allocator.shrink(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*shr.as_ptr().add(i), 0xCC);
        }
    }

    // error: shrink to a larger size
    let err = unsafe { allocator.shrink(shr, new, old).unwrap_err() };
    assert_eq!(
        err,
        AllocError::ShrinkBiggerNewLayout(new.size(), old.size())
    );

    // error: grow to a smaller size
    let err2 = unsafe { allocator.grow(shr, old, new).unwrap_err() };
    assert_eq!(
        err2,
        AllocError::GrowSmallerNewLayout(old.size(), new.size())
    );

    unsafe {
        allocator.dealloc(shr, new);
    }
}

#[test]
fn test_realloc_variants() {
    let allocator = DefaultAlloc;
    let old = Layout::from_size_align(4, 1).unwrap();
    let new = Layout::from_size_align(2, 1).unwrap();
    let ptr = allocator.alloc_filled(old, 0xDD).unwrap();
    // realloc shrink
    let rs = unsafe { allocator.realloc(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*rs.as_ptr().add(i), 0xDD);
        }
        allocator.dealloc(rs, new);
    }

    // realloc grow
    let ptr2 = allocator.alloc_zeroed(old).unwrap();
    let rg = unsafe {
        allocator
            .realloc_zeroed(ptr2, old, Layout::from_size_align(6, 1).unwrap())
            .unwrap()
    };
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*rg.as_ptr().add(i), 0);
        }
        for i in old.size()..6 {
            assert_eq!(*rg.as_ptr().add(i), 0);
        }
        allocator.dealloc(rg, Layout::from_size_align(6, 1).unwrap());
    }
}

#[test]
fn test_pad_layout_functions() {
    let layout = Layout::from_size_align(10, 4).unwrap();
    let padding_size = pad_layout_for(layout, 8);
    assert_eq!(padding_size, 6);

    let aligned_layout = pad_layout_to_align(layout, 8);
    assert_eq!(aligned_layout.align(), 4);
    assert!(aligned_layout.size() >= layout.size());
    assert_eq!(aligned_layout.size(), 16);
}

#[test]
fn test_repeat_layout_variants() {
    let layout = Layout::from_size_align(4, 4).unwrap();
    let (rep, count) = repeat_layout(layout, 3).unwrap();
    assert_eq!(count, 4);
    assert_eq!(rep.size(), 4 * 3);
    assert_eq!(rep.align(), 4);

    let rep_packed = repeat_layout_packed(layout, 5).unwrap();
    assert_eq!(rep_packed.size(), 4 * 5);
    assert_eq!(rep_packed.align(), 4);
}

#[cfg(feature = "alloc_ext")]
mod alloc_ext_tests {
    use super::*;
    use core::alloc::Layout;
    use memapi::{AllocExt, DefaultAlloc};

    #[test]
    fn test_alloc_init_and_default_and_write() {
        let allocator = DefaultAlloc;
        // alloc_init
        let ptr = allocator
            .alloc_init::<u32, _>(|p| unsafe { *p.as_ptr() = 42 })
            .unwrap();
        assert_eq!(unsafe { *ptr.as_ptr() }, 42);
        unsafe {
            allocator.dealloc(ptr.cast(), Layout::new::<u32>());
        }

        // alloc_default
        let dptr = allocator.alloc_default::<u32>().unwrap();
        assert_eq!(unsafe { *dptr.as_ptr() }, u32::default());
        unsafe {
            allocator.dealloc(dptr.cast(), Layout::new::<u32>());
        }

        // alloc_write
        let wptr = allocator.alloc_write(7u32).unwrap();
        assert_eq!(unsafe { *wptr.as_ptr() }, 7);
        unsafe {
            allocator.dealloc(wptr.cast(), Layout::new::<u32>());
        }
    }

    #[test]
    fn test_alloc_init_and_default_slice() {
        let allocator = DefaultAlloc;
        let len = 3;
        // alloc_init_slice
        let sptr = allocator
            .alloc_init_slice::<u32, _>(
                |p| {
                    let p = p.cast::<u32>();
                    for i in 0..len {
                        unsafe {
                            p.add(i).write(5);
                        }
                    }
                },
                len,
            )
            .unwrap();
        let slice_ref: &[u32] = unsafe { sptr.as_ref() };
        assert_eq!(slice_ref, &[5; 3]);
        unsafe {
            allocator.dealloc(sptr.cast(), Layout::array::<u32>(len).unwrap());
        }

        // alloc_default_slice
        let dptr = allocator.alloc_default_slice::<u32>(len).unwrap();
        let dslice: &[u32] = unsafe { dptr.as_ref() };
        assert_eq!(dslice, &[0; 3]);
        unsafe {
            allocator.dealloc(dptr.cast(), Layout::array::<u32>(len).unwrap());
        }
    }
}

#[cfg(feature = "stats")]
mod stats_gathering_tests {
    use core::{
        alloc::Layout,
        sync::atomic::{AtomicUsize, Ordering},
    };
    use memapi::stats::FmtLog;
    use memapi::{Alloc, DefaultAlloc, stats::Stats};
    use std::ops::Deref;

    #[test]
    fn test_stats_counts_correct() {
        let logger = AtomicUsize::new(0);
        let stats_alloc = Stats::new(DefaultAlloc, &logger);
        let layout = Layout::from_size_align(16, 8).unwrap();

        let ptr = stats_alloc.alloc(layout).expect("alloc failed");
        assert_eq!(
            logger.load(Ordering::SeqCst),
            layout.size(),
            "expected total bytes = {} after alloc",
            layout.size()
        );

        unsafe { stats_alloc.dealloc(ptr, layout) };
        assert_eq!(
            logger.load(Ordering::SeqCst),
            0,
            "expected total bytes = 0 after dealloc"
        );
    }

    #[test]
    fn test_stats_str_logger_test() {
        let logger = FmtLog::new(String::new());
        let stats_alloc = Stats::new(DefaultAlloc, &logger);

        let layout = Layout::from_size_align(16, 8).unwrap();

        let ptr = stats_alloc.alloc(layout).unwrap();

        unsafe {
            stats_alloc.dealloc(ptr, layout);
        }

        assert_eq!(
            *logger.get_log(),
            format!(
                "Successful initial allocation of 16 bytes with alignment 8 at {ptr:p}, and newly \
                allocated bytes being uninitialized. (16 total bytes allocated)\nDeallocation of \
                16 bytes with alignment 8 at {ptr:p}. (0 total bytes allocated)\n"
            )
        );
    }
}
