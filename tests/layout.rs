use {
    memapi2::{
        error::{AlignErr, LayoutErr},
        layout::Layout
    },
    std::alloc::Layout as StdLayout
};

#[test]
fn layout_from_stdlib() {
    let std_layout = StdLayout::from_size_align(1024, 1024).unwrap();
    let layout = Layout::from_stdlib(std_layout);

    assert_eq!(std_layout.size(), layout.size(), "size mismatch");
    assert_eq!(std_layout.align(), layout.align(), "align mismatch");

    assert_eq!(std_layout, layout.to_stdlib(), "back to stdlib mismatch");

    assert_eq!(std_layout, layout, "partialeq mismatch");
}

#[test]
fn layout_to_stdlib() {
    let layout = Layout::from_size_align(1024, 1024).unwrap();
    let std_layout = layout.to_stdlib();

    assert_eq!(layout.size(), std_layout.size(), "size mismatch");
    assert_eq!(layout.align(), std_layout.align(), "align mismatch");

    assert_eq!(layout, Layout::from_stdlib(std_layout), "back to custom mismatch");

    assert_eq!(layout, std_layout, "partialeq mismatch");
}

#[test]
fn from_size_align_invalid_zero_align() {
    let err = Layout::from_size_align(8, 0).unwrap_err();
    assert_eq!(err, LayoutErr::Align(AlignErr::ZeroAlign));
}

#[test]
fn from_size_align_invalid_non_power_of_two() {
    let err = Layout::from_size_align(8, 3).unwrap_err();
    assert_eq!(err, LayoutErr::Align(AlignErr::NonPowerOfTwoAlign(3)));
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
    assert_eq!(l.padding_needed_for(3), usize::MAX);
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
