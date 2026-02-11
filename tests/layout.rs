use {
    ::core::mem::{align_of, size_of},
    memapi2::{
        Layout,
        error::{Error, LayoutErr},
        helpers::USIZE_HIGH_BIT
    },
    std::alloc::Layout as StdLayout
};

#[test]
fn layout_from_stdlib() {
    let std_layout = StdLayout::from_size_align(1024, 64).unwrap();
    let layout = Layout::from_stdlib(std_layout);

    assert_eq!(std_layout.size(), layout.size(), "size mismatch");
    assert_eq!(std_layout.align(), layout.align(), "align mismatch");

    assert_eq!(std_layout, layout.to_stdlib(), "back to stdlib mismatch");

    assert_eq!(std_layout, layout, "partialeq mismatch");
}

#[test]
fn layout_to_stdlib() {
    let layout = Layout::from_size_align(1024, 64).unwrap();
    let std_layout = layout.to_stdlib();

    assert_eq!(layout.size(), std_layout.size(), "size mismatch");
    assert_eq!(layout.align(), std_layout.align(), "align mismatch");

    assert_eq!(layout, Layout::from_stdlib(std_layout), "back to custom mismatch");

    assert_eq!(layout, std_layout, "partialeq mismatch");
}

#[test]
fn from_size_align_invalid_zero_align() {
    let err = Layout::from_size_align(8, 0).unwrap_err();
    assert_eq!(err, Error::InvalidLayout(8, 0, LayoutErr::ZeroAlign));
}

#[test]
fn from_size_align_invalid_non_power_of_two() {
    let err = Layout::from_size_align(8, 3).unwrap_err();
    assert_eq!(err, Error::InvalidLayout(8, 3, LayoutErr::NonPowerOfTwoAlign));
}

#[test]
fn align_to() {
    let l = Layout::from_size_align(16, 8).unwrap();

    // no change if aligned to < align
    let l2 = l.align_to(4).unwrap();
    assert_eq!(l2.size(), 16);
    assert_eq!(l2.align(), 8);

    // same for == align
    let l3 = l.align_to(8).unwrap();
    assert_eq!(l3.size(), 16);
    assert_eq!(l3.align(), 8);

    // should change for higher align
    let l4 = l.align_to(16).unwrap();
    assert_eq!(l4.size(), 16);
    assert_eq!(l4.align(), 16);
}

#[test]
fn padding_needed_for_invalid() {
    let l = Layout::from_size_align(6, 8).unwrap();
    assert_eq!(
        l.padding_needed_for(3),
        Err(Error::InvalidLayout(6, 3, LayoutErr::NonPowerOfTwoAlign))
    );
}

#[test]
fn pad_to_align() {
    let l = Layout::from_size_align(6, 8).unwrap();
    let p = l.pad_to_align();
    assert_eq!(p.size(), 8);
    assert_eq!(p.align(), 8);
}

#[test]
fn repeat_and_repeat_packed() {
    // base layout with size not multiple of align
    let base = Layout::from_size_align(3, 2).unwrap();

    // repeat uses padded size as stride
    let (arr, stride) = base.repeat(3).unwrap();
    assert_eq!(stride, base.pad_to_align().size()); // 4
    assert_eq!(arr.size(), 12);
    assert_eq!(arr.align(), 2);

    // repeat_packed uses no padding
    let packed = base.repeat_packed(3).unwrap();
    assert_eq!(packed.size(), 9);
    assert_eq!(packed.align(), 2);
}

#[test]
fn array_layout_basic_and_zst() {
    let l = Layout::array::<u16>(3).unwrap();
    assert_eq!(l.size(), 6);
    assert_eq!(l.align(), 2);

    let zst = Layout::array::<()>(10).unwrap();
    assert_eq!(zst.size(), 0);
    assert_eq!(zst.align(), 1);
}

#[test]
fn array_layout_exceeds_max() {
    let max = (USIZE_HIGH_BIT - align_of::<u8>()) / size_of::<u8>();
    let err = Layout::array::<u8>(max + 1).unwrap_err();
    assert_eq!(err, Error::InvalidLayout(1, 1, LayoutErr::ExceedsMax));
}

#[test]
fn layout_for_value_slice() {
    let data = [10u16, 20, 30];
    let layout = Layout::for_value(&data[..]);
    assert_eq!(layout.size(), size_of::<u16>() * data.len());
    assert_eq!(layout.align(), align_of::<u16>());
}

#[test]
fn layout_for_value_raw() {
    let value = 42u32;
    let ptr = &value as *const u32;
    let layout = unsafe { Layout::for_value_raw(ptr) };
    assert_eq!(layout, Layout::new::<u32>());
}

#[test]
fn align_to_multiple_of_rounds_up() {
    let l = unsafe { Layout::from_size_align_unchecked(30, 8) };
    let rounded = l.align_to_multiple_of(16).unwrap();
    assert_eq!(rounded.align(), 16);
    assert_eq!(rounded.size(), 30);

    let same = rounded.align_to_multiple_of(8).unwrap();
    assert_eq!(same, rounded);
}

#[test]
fn aligned_alloc_compatible_roundtrip() {
    let original = Layout::from_size_align(10, 1).unwrap();
    let compatible = original.to_aligned_alloc_compatible().unwrap();
    let from_fn = Layout::aligned_alloc_compatible_from_size_align(10, 1).unwrap();
    let ptr_sz = size_of::<usize>();

    assert_eq!(compatible, from_fn);
    assert!(compatible.align() >= ptr_sz);
    assert_eq!(compatible.align() % ptr_sz, 0);
    assert_eq!(compatible.size() % compatible.align(), 0);
    assert!(compatible.size() >= original.size());
}
