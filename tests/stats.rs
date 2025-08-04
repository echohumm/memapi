use core::{
    alloc::Layout,
    sync::atomic::{AtomicUsize, Ordering},
};
use memapi::{
    stats::{FmtLog, Stats},
    Alloc,
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
    assert_eq!(
        logger.load(Ordering::SeqCst),
        0,
        "expected total bytes = 0 after dealloc"
    );
}

#[test]
fn test_stats_str_logger_test() {
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
            "Successful initial allocation of 16 bytes with alignment 8 at {ptr:p}, and newly \
                allocated bytes being uninitialized. (16 total bytes allocated)\nDeallocation of \
                16 bytes with alignment 8 at {ptr:p}. (0 total bytes allocated)\n"
        )
    );
}
