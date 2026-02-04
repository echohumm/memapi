// miri doesn't like non-standard c functions like stack_alloc relies on
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
                        // TODO: investigate this behavior:
                        // pointer: 0x7fcf2b2fd260 has good align of 32 (need 16)
                        // pointer: 0x7fcf2b2fd240 has good align of 64 (need 32)
                        // pointer: 0x7fcf2b2fd240 has good align of 64 (need 64)
                        // pointer: 0x7fcf2b2fd200 has good align of 512 (need 128)
                        // pointer: 0x7fcf2b2fd200 has good align of 512 (need 256)
                        // pointer: 0x7fcf2b2fd200 has good align of 512 (need 512)
                        // pointer: 0x7fcf2b2fd000 has good align of 4096 (need 1024)
                        // pointer: 0x7fcf2b2fd000 has good align of 4096 (need 2048)
                        // pointer: 0x7fcf2b2fd000 has good align of 4096 (need 4096)
                        // ---
                        // pointer: 0x7f50e3ae42d0 has good align of 16 (need 1)
                        // pointer: 0x7f50e3ae42d0 has good align of 16 (need 2)
                        // pointer: 0x7f50e3ae42d0 has good align of 16 (need 4)
                        // pointer: 0x7f50e3ae42d0 has good align of 16 (need 8)
                        // pointer: 0x7f50e3ae42d0 has good align of 16 (need 16)
                        // pointer: 0x7f50e3ae42c0 has good align of 64 (need 32)
                        // pointer: 0x7f50e3ae42c0 has good align of 64 (need 64)
                        // pointer: 0x7f50e3ae4280 has good align of 128 (need 128)
                        // pointer: 0x7f50e3ae4200 has good align of 512 (need 256)
                        // pointer: 0x7f50e3ae4200 has good align of 512 (need 512)
                        // pointer: 0x7f50e3ae4000 has good align of 16384 (need 1024)
                        // pointer: 0x7f50e3ae4000 has good align of 16384 (need 2048)
                        // pointer: 0x7f50e3ae4000 has good align of 16384 (need 4096)
                        eprintln!(
                            "pointer: {:p} only has align of {} (need {})",
                            ptr,
                            ptr_max_align(ptr),
                            align
                        );
                        // abort instead of unwind so we don't cause UB
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
