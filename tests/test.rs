use core::alloc::Layout;
use memapi::unstable_util::{
    pad_layout_for, pad_layout_to_align, repeat_layout, repeat_layout_packed,
};
use memapi::{error::AllocError, Alloc, DefaultAlloc};

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
    use core::alloc::Layout;
    use memapi::type_props::SizedProps;
    use memapi::{Alloc, AllocExt, DefaultAlloc};

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
    fn test_alloc_init_and_default_and_write() {
        let allocator = DefaultAlloc;
        // alloc_init
        let ptr = allocator
            .alloc_init::<u32, _>(|p| unsafe { *p.as_ptr() = 42 })
            .unwrap();
        assert_eq!(unsafe { *ptr.as_ptr() }, 42);
        unsafe {
            allocator.dealloc(ptr.cast(), u32::LAYOUT);
        }

        // alloc_default
        let dptr = allocator.alloc_default::<u32>().unwrap();
        assert_eq!(unsafe { *dptr.as_ptr() }, u32::default());
        unsafe {
            allocator.dealloc(dptr.cast(), u32::LAYOUT);
        }

        // alloc_write
        let wptr = allocator.alloc_write(7u32).unwrap();
        assert_eq!(unsafe { *wptr.as_ptr() }, 7);
        unsafe {
            allocator.dealloc(wptr.cast(), u32::LAYOUT);
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
        let gf = unsafe { allocator.grow_filled(ptr3, old, new, 0xBB).unwrap() };
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
}

#[cfg(feature = "alloc_slice")]
mod alloc_slice_tests {
    use core::alloc::Layout;
    use memapi::{alloc_slice::AllocSlice, Alloc, DefaultAlloc};

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

#[cfg(all(feature = "stats", feature = "std"))]
mod stats_gathering_tests {
    use core::{
        alloc::Layout,
        sync::atomic::{AtomicUsize, Ordering},
    };
    use memapi::{
        stats::{FmtLog, Stats},
        Alloc,
    };

    #[test]
    fn test_stats_counts_correct() {
        let logger = AtomicUsize::new(0);
        let stats_alloc = Stats::new(&logger);
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
        let stats_alloc = Stats::new(&logger);

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

#[cfg(feature = "owned")]
mod owned_tests {
    use memapi::{
        owned::{OwnedBuf, VariableError},
        DefaultAlloc,
    };

    #[test]
    fn test_new_and_basic_properties() {
        // create a buffer of 5 bytes
        let mut buf = OwnedBuf::<u8, DefaultAlloc>::new_in(5, DefaultAlloc).unwrap();
        assert_eq!(buf.size(), 5);
        assert_eq!(buf.initialized(), 0);
        assert_eq!(buf.buf().len(), 5);
        assert_eq!(buf.uninit_buf().len(), 5);
        assert_eq!(buf.init_buf().len(), 0);

        // fill it with try_init_next
        for i in 0..5u8 {
            buf.try_init_next(i).unwrap();
        }
        assert_eq!(buf.initialized(), 5);
        // values must match
        #[allow(clippy::cast_possible_truncation)]
        for (i, &val) in buf.init_buf().iter().enumerate() {
            assert_eq!(val, i as u8);
        }
        // further try_init_next returns Err with the value back
        let v = 0xFF;
        assert_eq!(buf.try_init_next(v).unwrap_err(), v);

        #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
        {
            buf.drop_and_dealloc();
        }
    }

    #[test]
    fn test_remove_and_replace_and_get() {
        let mut buf = OwnedBuf::<u32, DefaultAlloc>::new_in(5, DefaultAlloc).unwrap();
        for i in 0..5 {
            buf.try_init_next(i).unwrap();
        }
        assert_eq!(buf.initialized(), 5);

        // remove_last
        assert_eq!(buf.remove_last(), Some(4));
        assert_eq!(buf.initialized(), 4);

        // remove at index
        assert_eq!(buf.remove(1), Some(1));
        assert_eq!(buf.initialized(), 3);
        // oob remove returns None
        assert!(buf.remove(10).is_none());

        // replace_last
        let old = buf.replace_last(100).unwrap();
        assert_eq!(old, 3);
        assert_eq!(buf.init_buf().last().copied(), Some(100));

        // replace at index
        let old2 = buf.replace(1, 50).unwrap();
        assert_eq!(old2, 2);
        assert_eq!(*buf.get(1).unwrap(), 50);
        // get out of bounds
        assert!(buf.get(10).is_none());
        assert!(buf.get_ptr(10).is_none());
        assert!(buf.get_ptr(1).is_some());

        #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
        {
            buf.drop_and_dealloc();
        }
    }

    #[test]
    fn test_into_and_from_raw_parts() {
        let mut buf = OwnedBuf::<i16, DefaultAlloc>::new_in(4, DefaultAlloc).unwrap();
        for i in 0..4 {
            buf.try_init_next(i * 10).unwrap();
        }
        let init = buf.initialized();
        let size = buf.size();
        let (ptr, got_init, got_size, alloc) = buf.into_raw_parts();
        assert_eq!(got_init, init);
        assert_eq!(got_size, size);
        // rebuild
        let buf2 = unsafe { OwnedBuf::from_raw_parts(ptr, got_init, got_size, alloc) };
        assert_eq!(buf2.initialized(), init);
        assert_eq!(buf2.size(), size);
        // values are intact
        #[allow(clippy::cast_possible_truncation)]
        #[allow(clippy::cast_possible_wrap)]
        for (i, &v) in buf2.init_buf().iter().enumerate() {
            assert_eq!(v, (i as i16) * 10);
        }

        #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
        {
            buf2.drop_and_dealloc();
        }
    }

    #[test]
    fn test_try_insert_and_try_insert_grow() {
        let mut buf = OwnedBuf::<u8, DefaultAlloc>::new_in(3, DefaultAlloc).unwrap();
        // fill two
        buf.try_init_next(1).unwrap();
        buf.try_init_next(2).unwrap();
        assert_eq!(buf.initialized(), 2);

        // try_insert within capacity
        buf.try_insert(1, 99).unwrap();
        assert_eq!(buf.initialized(), 3);
        assert_eq!(*buf.get(1).unwrap(), 99);

        // further try_insert fails and returns Err
        assert_eq!(buf.try_insert(0, 77).unwrap_err(), 77);

        // try_insert_grow: start with capacity 1 buffer
        let mut buf2 = OwnedBuf::<u8, DefaultAlloc>::new_in(1, DefaultAlloc).unwrap();
        buf2.try_init_next(10).unwrap();
        assert_eq!(buf2.size(), 1);
        // this will grow
        buf2.init_next_grow(20).unwrap();
        assert!(buf2.size() >= 2);
        assert_eq!(buf2.initialized(), 2);
        assert_eq!(buf2.init_buf(), &[10, 20]);

        #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
        {
            buf.drop_and_dealloc();
            buf2.drop_and_dealloc();
        }
    }

    #[test]
    fn test_remove_slice() {
        let mut buf = OwnedBuf::<u32, DefaultAlloc>::new_in(16, DefaultAlloc).unwrap();
        for i in 0..16 {
            buf.try_init_next(i).unwrap();
        }
        // remove slice of length 3 at index 1
        let maybe_slice = buf.remove_slice(3, 3);
        assert!(maybe_slice.is_some());
        let slice_res = maybe_slice.unwrap().unwrap();
        assert_eq!(slice_res.initialized(), 3);
        assert_eq!(slice_res.size(), 3);
        assert_eq!(slice_res.init_buf(), &[3, 4, 5]);
        // original buffer should have had 6 init, now 13 left
        assert_eq!(buf.initialized(), 13);

        #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
        {
            buf.drop_and_dealloc();
            slice_res.drop_and_dealloc();
        }
    }

    #[test]
    fn test_debug_and_display_errors() {
        // Debug impl for OwnedBuf
        let buf = OwnedBuf::<u8, DefaultAlloc>::new_unallocated_in(DefaultAlloc);
        let s = format!("{buf:?}");
        assert!(s.contains("OwnedBuf"));

        // VariableError debug and display
        let soft: VariableError<&str, &str> = VariableError::Soft("oops");
        let hard: VariableError<&str, &str> = VariableError::Hard("boom");
        let ds = format!("{soft:?}");
        let dh = format!("{hard:?}");
        assert!(ds.contains("Soft"));
        assert!(dh.contains("Hard"));

        let ls = format!("{soft}");
        let lh = format!("{hard}");
        assert!(ls.contains("oops"));
        assert!(lh.contains("boom"));

        #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
        {
            buf.drop_and_dealloc();
        }
    }

    // #[test]
    // fn test_zst() {
    //     struct Zst;
    //
    //     let mut buf = OwnedBuf::<Zst>::new(8);
    // }
}

#[cfg(all(feature = "jemalloc", not(miri)))]
mod jemalloc_tests {
    use core::{alloc::Layout, slice};
    use memapi::{ffi::jem::usable_size, jemalloc::Jemalloc, type_props::SizedProps, Alloc};

    #[test]
    fn alloc_and_dealloc_basic() {
        let alloc = Jemalloc;
        let layout = Layout::from_size_align(64, 8).unwrap();

        unsafe {
            let ptr = alloc.alloc(layout).unwrap();
            // we can write into the block
            ptr.write_bytes(0xAB, layout.size());
            alloc.dealloc(ptr, layout);
        }
    }

    #[test]
    fn alloc_zeroed_is_really_zeroed() {
        let alloc = Jemalloc;
        let size = 128;
        let layout = Layout::from_size_align(size, 8).unwrap();

        unsafe {
            let ptr = alloc.alloc_zeroed(layout).unwrap();
            // treat as byte slice
            let buf = slice::from_raw_parts(ptr.as_ptr(), size);
            assert!(
                buf.iter().all(|&b| b == 0),
                "alloc_zeroed must produce all-zero bytes"
            );
            alloc.dealloc(ptr, layout);
        }
    }

    #[test]
    fn usable_size_at_least_requested() {
        let alloc = Jemalloc;
        let size = 100;
        let layout = Layout::from_size_align(size, 16).unwrap();

        unsafe {
            let ptr = alloc.alloc(layout).unwrap();
            let usable = usable_size(ptr.as_ptr());
            assert!(
                usable >= size,
                "usable_size {} should be >= requested {}",
                usable,
                size
            );
            alloc.dealloc(ptr, layout);
        }
    }

    #[test]
    #[allow(clippy::cast_possible_truncation)]
    fn realloc_preserves_initial_contents() {
        let alloc = Jemalloc;
        let old_count = 4;
        let old_layout = Layout::array::<u32>(old_count).unwrap();

        unsafe {
            // allocate and write a pattern
            let ptr = alloc.alloc(old_layout).unwrap().cast();
            for i in 0..old_count {
                ptr.add(i).write(i as u32 + 1);
            }

            // grow to twice as many elements
            let new_size = old_count * 2 * u32::SZ;
            let new_layout = Layout::from_size_align_unchecked(new_size, u32::ALIGN);
            let new_ptr = alloc
                .realloc(ptr.cast(), old_layout, new_layout)
                .unwrap()
                .cast();

            // original data should be intact
            for i in 0..old_count {
                let v: u32 = new_ptr.add(i).read();
                assert_eq!(v, i as u32 + 1);
            }

            // cleanup
            let new_layout = Layout::from_size_align(new_size, old_layout.align()).unwrap();
            alloc.dealloc(new_ptr.cast(), new_layout);
        }
    }
}
