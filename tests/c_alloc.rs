// miri is incompatible with windows' _aligned_alloc
#![cfg(all(feature = "c_alloc", not(all(windows, miri))))]

use {
    core::cmp,
    memapi2::{
        allocs::c_alloc::CAlloc,
        error::Error,
        layout::Layout,
        traits::{
            alloc::{Alloc, Dealloc, Grow, Shrink},
            data::type_props::SizedProps
        }
    },
    std::ptr
};

#[test]
fn test_alloc_and_dealloc() {
    let allocator = CAlloc;
    let layout = Layout::from_size_align(16, 8).unwrap();
    // Allocate
    let ptr = allocator.alloc(layout).expect("alloc failed");
    // Write and read
    unsafe {
        ptr::write_bytes(ptr.as_ptr(), 0xAB, layout.size());
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0xAB);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
fn test_alloc_zeroed() {
    let allocator = CAlloc;
    let layout = Layout::from_size_align(32, 8).unwrap();
    let ptr = allocator.zalloc(layout).expect("alloc_zeroed failed");
    unsafe {
        for i in 0..layout.size() {
            assert_eq!(*ptr.as_ptr().add(i), 0, "failed on byte {}", i);
        }
        allocator.dealloc(ptr, layout);
    }
}

#[test]
fn test_shrink_and_error_cases() {
    let allocator = CAlloc;
    let old = Layout::from_size_align(32, usize::SZ).unwrap();
    // 1 is fine here though because we already satisfy the alignment, and
    //  1 < MAXIMUM_GUARANTEED_ALIGNMENT
    let new = Layout::from_size_align(16, usize::SZ).unwrap();
    let ptr = allocator.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(ptr.as_ptr(), 0xCC, old.size());
    }
    let shr = unsafe { allocator.shrink(ptr, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*shr.as_ptr().add(i), 0xCC);
        }
    }

    // error: shrink to a larger size
    let err = unsafe { allocator.shrink(shr, new, old).unwrap_err() };
    assert_eq!(err, Error::ShrinkLargerNewLayout(new.size(), old.size()));

    // error: grow to a smaller size
    let err2 = unsafe { allocator.grow(shr, old, new).unwrap_err() };
    assert_eq!(err2, Error::GrowSmallerNewLayout(old.size(), new.size()));

    unsafe {
        allocator.dealloc(shr, new);
    }
}

#[test]
fn grow_preserves_prefix() {
    let a = CAlloc;
    let old = Layout::from_size_align(8, 8).unwrap();
    let new = Layout::from_size_align(16, 8).unwrap();

    let p = a.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0x11, old.size());
    }

    let grown = unsafe { a.grow(p, old, new).unwrap() };
    // first 8 bytes preserved
    unsafe {
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), 0x11);
        }
        a.dealloc(grown, new);
    }
}

#[test]
fn zgrow_zeros_new_region() {
    let a = CAlloc;
    let old = Layout::from_size_align(8, 8).unwrap();
    let new = Layout::from_size_align(16, 8).unwrap();

    let p = a.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0x22, old.size());
    }

    let grown = unsafe { a.zgrow(p, old, new).unwrap() };
    unsafe {
        // original region preserved
        for i in 0..old.size() {
            assert_eq!(*grown.as_ptr().add(i), 0x22);
        }
        // new region zeroed
        for i in old.size()..new.size() {
            assert_eq!(*grown.as_ptr().add(i), 0);
        }
        a.dealloc(grown, new);
    }
}

#[test]
fn shrink_preserves_prefix() {
    let a = CAlloc;
    let old = Layout::from_size_align(16, 8).unwrap();
    let new = Layout::from_size_align(8, 8).unwrap();

    let p = a.alloc(old).unwrap();
    unsafe {
        ptr::write_bytes(p.as_ptr(), 0xAB, old.size());
    }

    let shr = unsafe { a.shrink(p, old, new).unwrap() };
    unsafe {
        for i in 0..new.size() {
            assert_eq!(*shr.as_ptr().add(i), 0xAB);
        }
        a.dealloc(shr, new);
    }
}

#[test]
fn test_alloc_dealloc_var_alignments() {
    let a = CAlloc;
    let aligns = [1usize, 2, 4, 8, 16, 32];

    for &align in &aligns {
        let size = cmp::max(1, align * 2);
        let layout = Layout::from_size_align(size, align).unwrap();
        let ptr = a.alloc(layout).expect("alloc failed");
        unsafe {
            // fill with a distinctive pattern per alignment
            let pat = (align as u8).wrapping_mul(3).wrapping_add(1);
            ptr::write_bytes(ptr.as_ptr(), pat, layout.size());

            for i in 0..layout.size() {
                assert_eq!(*ptr.as_ptr().add(i), pat, "mismatch at align {} byte {}", align, i);
            }

            // pointer must satisfy alignment
            let p_usize = ptr.as_ptr() as usize;
            assert_eq!(
                p_usize % align,
                0,
                "returned pointer {:p} not aligned to {}",
                ptr.as_ptr(),
                align
            );

            a.dealloc(ptr, layout);
        }
    }
}

#[test]
fn test_grow_var_alignments_combinations() {
    let a = CAlloc;
    let aligns = [1usize, 2, 4, 8, 16, 32];

    for &old_align in &aligns {
        for &new_align in &aligns {
            // pick sizes such that new_size > old_size to exercise grow/zgrow
            let old_size = cmp::max(1, old_align * 2);
            let new_size = cmp::max(old_size + 1, new_align * 4);
            let old = Layout::from_size_align(old_size, old_align).unwrap();
            let new = Layout::from_size_align(new_size, new_align).unwrap();

            let p = a.alloc(old).expect("alloc failed");
            unsafe {
                // fill original region with pattern unique to (old_align, new_align)
                let pat = ((old_align + new_align) as u8).wrapping_mul(7);
                ptr::write_bytes(p.as_ptr(), pat, old.size());
            }

            // try grow (non-zeroing)
            match unsafe { a.grow(p, old, new) } {
                Ok(gptr) => unsafe {
                    // preserved prefix
                    for i in 0..old.size() {
                        assert_eq!(
                            *gptr.as_ptr().add(i),
                            ((old_align + new_align) as u8).wrapping_mul(7),
                            "grow: prefix not preserved (old_align {} new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    // pointer must satisfy new alignment
                    let g_usize = gptr.as_ptr() as usize;
                    assert_eq!(
                        g_usize % new_align,
                        0,
                        "grow: returned pointer {:p} not aligned to new_align {}",
                        gptr.as_ptr(),
                        new_align
                    );
                    a.dealloc(gptr, new);
                },
                Err(_e) => unsafe {
                    // grow failed: original pointer should remain valid. Verify and free.
                    for i in 0..old.size() {
                        assert_eq!(
                            *p.as_ptr().add(i),
                            ((old_align + new_align) as u8).wrapping_mul(7),
                            "grow-err: original allocation content corrupted (old_align {} \
                             new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    a.dealloc(p, old);
                }
            }
        }
    }
}

#[test]
fn test_zgrow_var_alignments_combinations() {
    let a = CAlloc;
    let aligns = [1usize, 2, 4, 8, 16, 32];

    for &old_align in &aligns {
        for &new_align in &aligns {
            // pick sizes such that new_size > old_size to exercise grow/zgrow
            let old_size = cmp::max(1, old_align * 2);
            let new_size = cmp::max(old_size + 1, new_align * 4);
            let old = Layout::from_size_align(old_size, old_align).unwrap();
            let new = Layout::from_size_align(new_size, new_align).unwrap();

            let p = a.alloc(old).expect("alloc failed (zgrow prep)");
            unsafe {
                let pat = ((old_align + new_align) as u8).wrapping_add(11);
                ptr::write_bytes(p.as_ptr(), pat, old.size());
            }

            match unsafe { a.zgrow(p, old, new) } {
                Ok(gptr) => unsafe {
                    // original region preserved
                    for i in 0..old.size() {
                        assert_eq!(
                            *gptr.as_ptr().add(i),
                            ((old_align + new_align) as u8).wrapping_add(11),
                            "zgrow: prefix not preserved (old_align {} new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    // new region zeroed
                    for i in old.size()..new.size() {
                        assert_eq!(
                            *gptr.as_ptr().add(i),
                            0,
                            "zgrow: new region not zeroed (old_align {} new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    // pointer alignment check
                    let g_usize = gptr.as_ptr() as usize;
                    assert_eq!(
                        g_usize % new_align,
                        0,
                        "zgrow: returned pointer {:p} not aligned to new_align {}",
                        gptr.as_ptr(),
                        new_align
                    );
                    a.dealloc(gptr, new);
                },
                Err(_e) => unsafe {
                    // zgrow failed: original pointer should remain valid. Verify and free.
                    for i in 0..old.size() {
                        assert_eq!(
                            *p.as_ptr().add(i),
                            ((old_align + new_align) as u8).wrapping_add(11),
                            "zgrow-err: original allocation content corrupted (old_align {} \
                             new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    a.dealloc(p, old);
                }
            }
        }
    }
}

#[test]
fn test_shrink_var_alignments_combinations() {
    let a = CAlloc;
    let aligns = [1usize, 2, 4, 8, 16, 32];

    for &old_align in &aligns {
        for &new_align in &aligns {
            // pick sizes such that old_size > new_size to exercise shrink
            let new_size = cmp::max(1, new_align * 2);
            let old_size = cmp::max(new_size + 1, old_align * 4);
            let old = Layout::from_size_align(old_size, old_align).unwrap();
            let new = Layout::from_size_align(new_size, new_align).unwrap();

            let p = a.alloc(old).expect("alloc failed");
            unsafe {
                let pat = ((old_align ^ new_align) as u8).wrapping_add(5);
                ptr::write_bytes(p.as_ptr(), pat, old.size());
            }

            match unsafe { a.shrink(p, old, new) } {
                Ok(sptr) => unsafe {
                    // prefix preserved (up to new.size())
                    for i in 0..new.size() {
                        assert_eq!(
                            *sptr.as_ptr().add(i),
                            ((old_align ^ new_align) as u8).wrapping_add(5),
                            "shrink: prefix not preserved (old_align {} new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    // ensure returned pointer meets new alignment
                    let s_usize = sptr.as_ptr() as usize;
                    assert_eq!(
                        s_usize % new_align,
                        0,
                        "shrink: returned pointer {:p} not aligned to new_align {}",
                        sptr.as_ptr(),
                        new_align
                    );
                    a.dealloc(sptr, new);
                },
                Err(_e) => unsafe {
                    // shrink failed: verify original still valid and free it
                    for i in 0..old.size() {
                        assert_eq!(
                            *p.as_ptr().add(i),
                            ((old_align ^ new_align) as u8).wrapping_add(5),
                            "shrink-err: original allocation content corrupted (old_align {} \
                             new_align {}) at byte {}",
                            old_align,
                            new_align,
                            i
                        );
                    }
                    a.dealloc(p, old);
                }
            }
        }
    }
}
