extern crate alloc;

use alloc::alloc::Layout;
use core::{hint::black_box, time::Duration};
use criterion::{criterion_main, Criterion};
use memapi::{type_props::SizedProps, AllocExt, DefaultAlloc};

fn bench_alloc_dealloc(c: &mut Criterion) {
    c.bench_function("alloc", |b| {
        b.iter(|| {
            let alloc = black_box(DefaultAlloc);
            let mem = black_box(black_box(alloc.alloc_write(black_box(193874_usize))).unwrap());
            unsafe {
                alloc.drop_and_dealloc(mem);
            }
        });
    });
}

fn bench_alloc_default_u64(c: &mut Criterion) {
    c.bench_function("alloc_default<u64>", |b| {
        b.iter(|| {
            let alloc = black_box(DefaultAlloc);
            let ptr = black_box(alloc.alloc_default::<u64>()).unwrap();
            unsafe {
                alloc.drop_and_dealloc(ptr);
            }
        });
    });
}

fn bench_alloc_write_u128(c: &mut Criterion) {
    c.bench_function("alloc_write<u128>", |b| {
        b.iter(|| {
            let alloc = black_box(DefaultAlloc);
            let value = black_box(0xDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_u128);
            let ptr = black_box(alloc.alloc_write::<u128>(value)).unwrap();
            unsafe {
                alloc.drop_and_dealloc(ptr);
            }
        });
    });
}

fn bench_alloc_filled_1k(c: &mut Criterion) {
    c.bench_function("alloc_filled_1k", |b| {
        b.iter(|| {
            let alloc = black_box(DefaultAlloc);
            let layout = unsafe {
                black_box(Layout::from_size_align_unchecked(
                    black_box(1024),
                    black_box(1),
                ))
            };
            let byte = black_box(0xA5_u8);
            let ptr = black_box(alloc.alloc_filled(layout, byte)).unwrap();
            unsafe {
                alloc.zero_and_dealloc(ptr, layout);
            }
        });
    });
}

fn bench_alloc_patterned_2k(c: &mut Criterion) {
    c.bench_function("alloc_patterned_2k", |b| {
        b.iter(|| {
            let alloc = black_box(DefaultAlloc);
            let layout = unsafe {
                black_box(Layout::from_size_align_unchecked(
                    black_box(2048),
                    black_box(1),
                ))
            };
            let ptr =
                black_box(alloc.alloc_patterned(layout, |i| black_box((i as u8).wrapping_mul(31))))
                    .unwrap();
            unsafe {
                alloc.zero_and_dealloc(ptr, layout);
            }
        });
    });
}

fn bench_grow_filled_1k_to_4k(c: &mut Criterion) {
    c.bench_function("grow_filled_1k_to_4k", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let old_layout = black_box(Layout::from_size_align_unchecked(
                black_box(1024),
                black_box(1),
            ));
            let new_layout = black_box(Layout::from_size_align_unchecked(
                black_box(4096),
                black_box(1),
            ));
            let ptr = black_box(alloc.alloc_filled(old_layout, black_box(0x11_u8))).unwrap();

            let grown = black_box(
                alloc
                    .grow_filled(ptr, old_layout, new_layout, black_box(0x22_u8))
                    .unwrap(),
            );

            alloc.zero_and_dealloc(grown, new_layout);
        });
    });
}

fn bench_realloc_filled_4k_to_1k(c: &mut Criterion) {
    c.bench_function("realloc_filled_4k_to_1k", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let old_layout = black_box(Layout::from_size_align_unchecked(
                black_box(4096),
                black_box(1),
            ));
            let new_layout = black_box(Layout::from_size_align_unchecked(
                black_box(1024),
                black_box(1),
            ));
            let ptr = black_box(alloc.alloc_filled(old_layout, black_box(0xEE_u8))).unwrap();

            let shrunk = black_box(
                alloc
                    .realloc_filled(ptr, old_layout, new_layout, black_box(0xFF_u8))
                    .unwrap(),
            );

            alloc.zero_and_dealloc(shrunk, new_layout);
        });
    });
}

fn bench_dealloc_typed_usize(c: &mut Criterion) {
    c.bench_function("dealloc_typed<usize>", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let ptr = black_box(alloc.alloc_write::<usize>(black_box(193874_usize))).unwrap();
            alloc.dealloc_typed(ptr);
        });
    });
}

fn bench_zero_and_dealloc_8k(c: &mut Criterion) {
    c.bench_function("zero_and_dealloc_8k", |b| {
        b.iter(|| unsafe {
            let alloc = black_box(DefaultAlloc);
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(8192),
                black_box(1),
            ));
            let ptr = black_box(alloc.alloc_filled(layout, black_box(0x77_u8))).unwrap();
            alloc.zero_and_dealloc(ptr, layout);
        });
    });
}

fn bench_alloc_dealloc_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(usize::SZ),
                black_box(usize::ALN),
            ));
            let mem = black_box(alloc(black_box(layout)));
            mem.cast::<usize>().write(black_box(193874));
            dealloc(mem, black_box(layout));
        });
    });
}

fn bench_alloc_default_u64_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_default<u64>", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(u64::SZ),
                black_box(u64::ALN),
            ));
            let mem = black_box(alloc(black_box(layout)));
            mem.cast::<u64>().write(black_box(u64::default()));
            dealloc(mem, black_box(layout));
        });
    });
}

fn bench_alloc_write_u128_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_write<u128>", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(u128::SZ),
                black_box(u128::ALN),
            ));
            let mem = black_box(alloc(black_box(layout)));
            let value = black_box(0xDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_u128);
            mem.cast::<u128>().write(value);
            dealloc(mem, black_box(layout));
        });
    });
}

fn bench_alloc_filled_1k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_filled_1k", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(1024),
                black_box(1),
            ));
            let byte = black_box(0xA5_u8);
            let mem = black_box(alloc(black_box(layout)));
            core::ptr::write_bytes(mem, byte, layout.size());
            core::ptr::write_bytes(mem, 0u8, layout.size());
            dealloc(mem, black_box(layout));
        });
    });
}

fn bench_alloc_patterned_2k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_alloc_patterned_2k", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(2048),
                black_box(1),
            ));
            let mem = black_box(alloc(black_box(layout)));
            let size = layout.size();
            for i in 0..size {
                let v = black_box((i as u8).wrapping_mul(31));
                mem.add(i).write(v);
            }
            core::ptr::write_bytes(mem, 0u8, size);
            dealloc(mem, black_box(layout));
        });
    });
}

fn bench_grow_filled_1k_to_4k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc, realloc};

    c.bench_function("base_grow_filled_1k_to_4k", |b| {
        b.iter(|| unsafe {
            let old_layout = black_box(Layout::from_size_align_unchecked(
                black_box(1024),
                black_box(1),
            ));
            let new_layout = black_box(Layout::from_size_align_unchecked(
                black_box(4096),
                black_box(1),
            ));
            let ptr = black_box(alloc(black_box(old_layout)));
            core::ptr::write_bytes(ptr, black_box(0x11_u8), old_layout.size());

            let grown = black_box(realloc(
                black_box(ptr),
                black_box(old_layout),
                black_box(new_layout.size()),
            ));
            // Fill the newly added tail region
            core::ptr::write_bytes(
                grown.add(old_layout.size()),
                black_box(0x22_u8),
                new_layout.size() - old_layout.size(),
            );

            core::ptr::write_bytes(grown, 0u8, new_layout.size());
            dealloc(grown, black_box(new_layout));
        });
    });
}

fn bench_realloc_filled_4k_to_1k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc, realloc};

    c.bench_function("base_realloc_filled_4k_to_1k", |b| {
        b.iter(|| unsafe {
            let old_layout = black_box(Layout::from_size_align_unchecked(
                black_box(4096),
                black_box(1),
            ));
            let new_layout = black_box(Layout::from_size_align_unchecked(
                black_box(1024),
                black_box(1),
            ));
            let ptr = black_box(alloc(black_box(old_layout)));
            // Initial fill
            core::ptr::write_bytes(ptr, black_box(0xEE_u8), old_layout.size());
            // Pre-fill the soon-to-be-freed tail region before shrinking
            core::ptr::write_bytes(
                ptr.add(new_layout.size()),
                black_box(0xFF_u8),
                old_layout.size() - new_layout.size(),
            );

            let shrunk = black_box(realloc(
                black_box(ptr),
                black_box(old_layout),
                black_box(new_layout.size()),
            ));
            core::ptr::write_bytes(shrunk, 0u8, new_layout.size());
            dealloc(shrunk, black_box(new_layout));
        });
    });
}

fn bench_dealloc_typed_usize_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_dealloc_typed<usize>", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(usize::SZ),
                black_box(usize::ALN),
            ));
            let mem = black_box(alloc(black_box(layout)));
            mem.cast::<usize>().write(black_box(193874_usize));
            dealloc(mem, black_box(layout));
        });
    });
}

fn bench_zero_and_dealloc_8k_base(c: &mut Criterion) {
    use alloc::alloc::{alloc, dealloc};

    c.bench_function("base_zero_and_dealloc_8k", |b| {
        b.iter(|| unsafe {
            let layout = black_box(Layout::from_size_align_unchecked(
                black_box(8192),
                black_box(1),
            ));
            let mem = black_box(alloc(black_box(layout)));
            core::ptr::write_bytes(mem, black_box(0x77_u8), layout.size());
            core::ptr::write_bytes(mem, 0u8, layout.size());
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
    bench_alloc_default_u64(&mut criterion);
    bench_alloc_write_u128(&mut criterion);
    bench_alloc_filled_1k(&mut criterion);
    bench_alloc_patterned_2k(&mut criterion);
    bench_grow_filled_1k_to_4k(&mut criterion);
    bench_realloc_filled_4k_to_1k(&mut criterion);
    bench_dealloc_typed_usize(&mut criterion);
    bench_zero_and_dealloc_8k(&mut criterion);
}

pub fn base_benches() {
    let mut criterion = get_criter();

    bench_alloc_dealloc_base(&mut criterion);
    bench_alloc_default_u64_base(&mut criterion);
    bench_alloc_write_u128_base(&mut criterion);
    bench_alloc_filled_1k_base(&mut criterion);
    bench_alloc_patterned_2k_base(&mut criterion);
    bench_grow_filled_1k_to_4k_base(&mut criterion);
    bench_realloc_filled_4k_to_1k_base(&mut criterion);
    bench_dealloc_typed_usize_base(&mut criterion);
    bench_zero_and_dealloc_8k_base(&mut criterion);
}

criterion_main!(crate_benches, base_benches);
