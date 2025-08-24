#[cfg(not(feature = "no_alloc"))] extern crate alloc;
extern crate criterion;

use {
	core::{hint::black_box, time::Duration},
	criterion::{Criterion, criterion_main},
	memapi::{Alloc, AllocExt, Layout, external::jemalloc::Jemalloc, data::type_props::SizedProps},
	std::ptr
};

fn bench_alloc_dealloc(c: &mut Criterion) {
    c.bench_function("alloc_dealloc", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(Jemalloc);
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
            let alloc = black_box(Jemalloc);
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
            let alloc = black_box(Jemalloc);
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
            let alloc = black_box(Jemalloc);
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

fn get_criter() -> Criterion {
    Criterion::default()
        .sample_size(10_000)
        .nresamples(150_000)
        .measurement_time(Duration::from_secs(8))
        .configure_from_args()
}

pub fn benches() {
    let mut criterion = get_criter();

    bench_alloc_dealloc(&mut criterion);
    bench_alloc_filled_1k(&mut criterion);
    bench_grow_filled_1k_to_4k(&mut criterion);
    bench_realloc_filled_4k_to_1k(&mut criterion);
}

criterion_main!(benches);
