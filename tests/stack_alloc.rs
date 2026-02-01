use {
    memapi2::{AllocTemp, Layout, helpers::ptr_max_align, stack_alloc::StackAlloc},
    std::process::abort
};

#[test]
fn stack_alloc() {
    unsafe {
        assert!(
            StackAlloc
                .alloc_temp(Layout::from_size_align(8, 8).unwrap(), |ptr| {
                    if ptr.as_ptr() as usize % 8 != 0 {
                        eprintln!(
                            "pointer: {:p} only has align of {} (need 8)",
                            ptr,
                            ptr_max_align(ptr)
                        );
                        // let's not cause ub lol
                        abort();
                    } else {
                        println!("pointer: {:p} has align of {} (need 8)", ptr, ptr_max_align(ptr));
                    }
                })
                .is_ok()
        )
    }
}
