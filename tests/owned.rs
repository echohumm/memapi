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
    let s = format!("{:?}", buf);
    assert!(s.contains("OwnedBuf"));

    // VariableError debug and display
    let soft: VariableError<&str, &str> = VariableError::Soft("oops");
    let hard: VariableError<&str, &str> = VariableError::Hard("boom");
    let ds = format!("{:?}", soft);
    let dh = format!("{:?}", hard);
    assert!(ds.contains("Soft"));
    assert!(dh.contains("Hard"));

    let ls = format!("{}", soft);
    let lh = format!("{}", hard);
    assert!(ls.contains("oops"));
    assert!(lh.contains("boom"));

    #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
    {
        buf.drop_and_dealloc();
    }
}

#[test]
fn test_zst() {
    #[derive(Debug, PartialEq, Eq)]
    struct Zst;

    let mut buf = OwnedBuf::<Zst>::new(8).unwrap();
    for _ in 0..8 {
        assert_eq!(buf.try_init_next(Zst), Ok(()));
    }
    
    assert_eq!(buf.try_init_next(Zst), Err(Zst));

    #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
    {
        buf.drop_and_dealloc();
    }
}

#[test]
fn test_init_next_slice() {
    let mut buf = OwnedBuf::<usize>::new(8).unwrap();
    
    unsafe {
        buf.init_next_unchecked(9);
    }
    
    let mut buf2 = buf.clone();
    let mut buf3 = buf.clone();
    
    #[cfg(not(any(feature = "drop_for_owned", feature = "zero_drop_for_owned")))]
    {
        buf.drop_and_dealloc();
    }
}

// TODO: test other slice operations and specialized stuff like clone_into
