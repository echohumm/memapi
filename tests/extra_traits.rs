use {
    core::ptr,
    memapi2::{
        Alloc,
        Dealloc,
        DefaultAlloc,
        Layout,
        traits::{Grow, Shrink}
    }
};

#[test]
fn grow_preserves_prefix() {
    let a = DefaultAlloc;
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
    let a = DefaultAlloc;
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
    let a = DefaultAlloc;
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
