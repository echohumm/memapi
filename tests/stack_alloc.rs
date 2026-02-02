#![cfg(not(miri))]
use {
    memapi2::{AllocTemp, Layout, helpers::ptr_max_align, stack_alloc::StackAlloc},
    std::process::abort
};

#[test]
fn stack_alloc() {
    for &align in &[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096] {
        assert!(
            unsafe {
                StackAlloc.alloc_temp(Layout::from_size_align(8, align).unwrap(), |ptr| {
                    if ptr.as_ptr() as usize % align != 0 {
                        eprintln!(
                            "pointer: {:p} only has align of {} (need {})",
                            ptr,
                            ptr_max_align(ptr),
                            align
                        );
                        abort();
                    } else {
                        println!(
                            "pointer: {:p} has good align of {} (need {})",
                            ptr,
                            ptr_max_align(ptr),
                            align
                        );
                    }
                })
            }
            .is_ok()
        )
    }
}

#[rustversion::since(1.71)]
#[test]
#[should_panic = "no UB? yippee!"]
fn stack_alloc_unwind() {
    unsafe {
        assert!(
            StackAlloc
                .alloc_temp::<(), _>(Layout::from_size_align(8, 8).unwrap(), |ptr| {
                    ptr.cast::<u64>().write(0xAAAAAAAAAAAAAAAA);
                    panic!("no UB? yippee!");
                })
                .is_ok()
        );
    }
}
