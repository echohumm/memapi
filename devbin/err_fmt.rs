#![allow(clippy::vec_init_then_push)]

use core::alloc::Layout;
use core::ptr::NonNull;
use memapi::error::{AllocError, ArithOp, ArithOverflow, Cause, InvLayout, LayoutErr};

fn main() {
    let l1 = Layout::from_size_align(8, 8).expect("layout ok");
    let l2 = Layout::from_size_align(16, 8).expect("layout ok");
    let dangling = NonNull::<u8>::dangling();

    let inv_layout = InvLayout(1, 0, LayoutErr::ZeroAlign);
    let arith = ArithOverflow(usize::MAX, ArithOp::Add, 1);

    let mut items: Vec<AllocError> = Vec::new();

    // AllocFailed with different causes (excluding OSErr)
    items.push(AllocError::AllocFailed(l1, Cause::Unknown));
    items.push(AllocError::AllocFailed(l2, Cause::OutOfMemory));

    // DeallocFailed
    #[cfg(feature = "fallible_dealloc")]
    {
        items.push(AllocError::DeallocFailed(
            dangling,
            l1,
            Cause::InvalidBlockStatus(memapi::fallible_dealloc::BlockStatus::NotOwned),
        ));

        items.push(AllocError::DeallocFailed(
            dangling,
            l1,
            Cause::InvalidBlockStatus(memapi::fallible_dealloc::BlockStatus::OwnedIncomplete(
                Some(l2),
            )),
        ));

        items.push(AllocError::DeallocFailed(
            dangling,
            l1,
            Cause::InvalidBlockStatus(memapi::fallible_dealloc::BlockStatus::Misaligned(Some(1))),
        ));
    }

    items.push(AllocError::InvalidLayout(inv_layout));

    items.push(AllocError::ZeroSizedLayout(dangling));

    items.push(AllocError::GrowSmallerNewLayout(1024, 256));
    items.push(AllocError::ShrinkBiggerNewLayout(256, 1024));

    items.push(AllocError::ArithmeticOverflow(arith));

    items.push(AllocError::Other("some static error"));

    for err in items {
        println!("---- Debug ----\n{:?}\n", err);
        println!("---- Display ----\n{}\n", err);
    }
}
