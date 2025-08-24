// miri is incompatible with malloc_defaultalloc
#![cfg_attr(feature = "malloc_defaultalloc", cfg(not(miri)))]
#![cfg(any(not(feature = "no_alloc"), feature = "malloc_defaultalloc"))]
#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
use {
    core::sync::atomic::{AtomicUsize, Ordering},
    memapi::{
        Alloc,
        Layout,
        stats::{FmtLog, Stats}
    }
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
    assert_eq!(logger.load(Ordering::SeqCst), 0, "expected total bytes = 0 after dealloc");
}

#[test]
fn test_stats_str_logger() {
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
            "Successful initial allocation of 16 bytes with alignment 8 at {p:p}, and newly \
             allocated bytes being uninitialized. (16 total bytes allocated)\nDeallocation of 16 \
             bytes with alignment 8 at {p:p}. (0 total bytes allocated)\n",
            p = ptr
        )
    );
}
