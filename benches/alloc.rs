#[cfg(not(feature = "no_alloc"))] extern crate alloc;
extern crate criterion;

use {
    core::{hint::black_box, time::Duration},
    criterion::{Criterion, criterion_main},
    memapi::{Alloc, AllocExt, DefaultAlloc, Layout, data::type_props::SizedProps},
    std::ptr
};

fn bench_alloc_dealloc(c: &mut Criterion) {
    c.bench_function("alloc_dealloc", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(usize::SZ),
                black_box(usize::ALN)
            ));
            let mem = black_box(alloc.alloc(black_box(layout))).unwrap();
            mem.as_ptr().cast::<usize>().write(black_box(193874));
            alloc.dealloc(mem, black_box(layout));
        });
    });
}

fn bench_alloc_filled_1k(c: &mut Criterion) {
    c.bench_function("alloc_filled_1k", |b| {
        b.iter(|| {
            let alloc = black_box(DefaultAlloc);
            let layout = unsafe {
                black_box(Layout::from_size_align_unchecked(black_box(1024), black_box(1)))
            };
            let byte = black_box(0xA5_u8);
            let ptr = black_box(alloc.falloc(layout, byte)).unwrap();
            unsafe {
                ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
                alloc.dealloc(ptr, layout);
            }
        });
    });
}

fn bench_grow_filled_1k_to_4k(c: &mut Criterion) {
    c.bench_function("grow_filled_1k_to_4k", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let old_layout =
                black_box(Layout::from_size_align_unchecked(black_box(1024), black_box(1)));
            let new_layout =
                black_box(Layout::from_size_align_unchecked(black_box(4096), black_box(1)));
            let ptr = black_box(alloc.falloc(old_layout, black_box(0x11_u8))).unwrap();

            let grown =
                black_box(alloc.fgrow(ptr, old_layout, new_layout, black_box(0x22_u8)).unwrap());

            ptr::write_bytes(grown.as_ptr(), 0, new_layout.size());
            alloc.dealloc(grown, new_layout);
        });
    });
}

fn bench_realloc_filled_4k_to_1k(c: &mut Criterion) {
    c.bench_function("realloc_filled_4k_to_1k", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let old_layout =
                black_box(Layout::from_size_align_unchecked(black_box(4096), black_box(1)));
            let new_layout =
                black_box(Layout::from_size_align_unchecked(black_box(1024), black_box(1)));
            let ptr = black_box(alloc.falloc(old_layout, black_box(0xEE_u8))).unwrap();

            let shrunk =
                black_box(alloc.refalloc(ptr, old_layout, new_layout, black_box(0xFF_u8)).unwrap());

            ptr::write_bytes(shrunk.as_ptr(), 0, new_layout.size());
            alloc.dealloc(shrunk, new_layout);
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_alloc_dealloc_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(usize::SZ),
                black_box(usize::ALN)
            ));
            let mem = black_box(alloc(black_box(layout)));
            mem.cast::<usize>().write(black_box(193874));
            dealloc(mem, black_box(layout));
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_alloc_default_u64_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_default<u64>", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(u64::SZ),
                black_box(u64::ALN)
            ));
            let mem = black_box(alloc(black_box(layout)));
            mem.cast::<u64>().write(black_box(u64::default()));
            dealloc(mem, black_box(layout));
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_alloc_write_u128_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_write<u128>", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(u128::SZ),
                black_box(u128::ALN)
            ));
            let mem = black_box(alloc(black_box(layout)));
            let value = black_box(0xDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_u128);
            mem.cast::<u128>().write(value);
            dealloc(mem, black_box(layout));
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_alloc_filled_1k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_filled_1k", |b| {
        b.iter(|| unsafe {
            let layout =
                black_box(Layout::from_size_align_unchecked(black_box(1024), black_box(1)));
            let byte = black_box(0xA5_u8);
            let mem = black_box(alloc(black_box(layout)));
            core::ptr::write_bytes(mem, byte, layout.size());
            core::ptr::write_bytes(mem, 0u8, layout.size());
            dealloc(mem, black_box(layout));
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_grow_filled_1k_to_4k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc, realloc};

    c.bench_function("base_grow_filled_1k_to_4k", |b| {
        b.iter(|| unsafe {
            let old_layout =
                black_box(Layout::from_size_align_unchecked(black_box(1024), black_box(1)));
            let new_layout =
                black_box(Layout::from_size_align_unchecked(black_box(4096), black_box(1)));
            let ptr = black_box(alloc(black_box(old_layout)));
            core::ptr::write_bytes(ptr, black_box(0x11_u8), old_layout.size());

            let grown = black_box(realloc(
                black_box(ptr),
                black_box(old_layout),
                black_box(new_layout.size())
            ));
            // Fill the newly added tail region
            core::ptr::write_bytes(
                grown.add(old_layout.size()),
                black_box(0x22_u8),
                new_layout.size() - old_layout.size()
            );

            core::ptr::write_bytes(grown, 0u8, new_layout.size());
            dealloc(grown, black_box(new_layout));
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_realloc_filled_4k_to_1k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc, realloc};

    c.bench_function("base_realloc_filled_4k_to_1k", |b| {
        b.iter(|| unsafe {
            let old_layout =
                black_box(Layout::from_size_align_unchecked(black_box(4096), black_box(1)));
            let new_layout =
                black_box(Layout::from_size_align_unchecked(black_box(1024), black_box(1)));
            let ptr = black_box(alloc(black_box(old_layout)));
            // Initial fill
            core::ptr::write_bytes(ptr, black_box(0xEE_u8), old_layout.size());
            // Pre-fill the soon-to-be-freed tail region before shrinking
            core::ptr::write_bytes(
                ptr.add(new_layout.size()),
                black_box(0xFF_u8),
                old_layout.size() - new_layout.size()
            );

            let shrunk = black_box(realloc(
                black_box(ptr),
                black_box(old_layout),
                black_box(new_layout.size())
            ));
            core::ptr::write_bytes(shrunk, 0u8, new_layout.size());
            dealloc(shrunk, black_box(new_layout));
        });
    });
}

#[cfg(not(feature = "no_alloc"))]
fn bench_dealloc_typed_usize_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_dealloc_typed<usize>", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(usize::SZ),
                black_box(usize::ALN)
            ));
            let mem = black_box(alloc(black_box(layout)));
            mem.cast::<usize>().write(black_box(193874_usize));
            dealloc(mem, black_box(layout));
        });
    });
}

fn get_criter() -> Criterion {
    Criterion::default()
        .sample_size(10_000)
        .nresamples(150_000)
        .measurement_time(Duration::from_secs(8))
        .configure_from_args()
}

pub fn crate_benches() {
    let mut criterion = get_criter();

    bench_alloc_dealloc(&mut criterion);
    bench_alloc_filled_1k(&mut criterion);
    bench_grow_filled_1k_to_4k(&mut criterion);
    bench_realloc_filled_4k_to_1k(&mut criterion);
}

#[cfg(not(feature = "no_alloc"))]
pub fn base_benches() {
    let mut criterion = get_criter();

    bench_alloc_dealloc_base(&mut criterion);
    bench_alloc_filled_1k_base(&mut criterion);
    bench_grow_filled_1k_to_4k_base(&mut criterion);
    bench_realloc_filled_4k_to_1k_base(&mut criterion);
}

#[cfg(feature = "no_alloc")]
pub fn base_benches() {
    println!("No base benchmarks available for no_alloc");
}

criterion_main!(crate_benches, base_benches);
