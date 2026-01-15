extern crate criterion;
extern crate memapi2;

use {
    core::hint::black_box,
    criterion::Criterion,
    memapi2::{Layout, data::type_props::SizedProps}
};

fn to_aligned_alloc_compatible(c: &mut Criterion) {
    let mut group = c.benchmark_group("taac");

    let noop = unsafe { Layout::from_size_align_unchecked(usize::SZ, usize::ALN) };
    let round_size = unsafe { Layout::from_size_align_unchecked(usize::SZ - 2, usize::ALN) };
    let round_align = unsafe { Layout::from_size_align_unchecked(usize::SZ, usize::ALN - 2) };
    let round_both = unsafe { Layout::from_size_align_unchecked(usize::SZ - 2, usize::ALN - 2) };

    group.bench_function("noop", |c| {
        c.iter(|| {
            let _ = black_box(black_box(noop).to_aligned_alloc_compatible());
        });
    });

    group.bench_function("round_size", |c| {
        c.iter(|| {
            let _ = black_box(black_box(round_size).to_aligned_alloc_compatible());
        });
    });

    group.bench_function("round_align", |c| {
        c.iter(|| {
            let _ = black_box(black_box(round_align).to_aligned_alloc_compatible());
        });
    });

    group.bench_function("round_both", |c| {
        c.iter(|| {
            let _ = black_box(black_box(round_both).to_aligned_alloc_compatible());
        });
    });
}

fn aligned_alloc_compatible_from_size_align(c: &mut Criterion) {
    let mut group = c.benchmark_group("aacfsa");

    let noop = (usize::SZ, usize::ALN);
    let round_size = (usize::SZ - 2, usize::ALN);
    let round_align = (usize::SZ, usize::SZ - 2);
    let round_both = (usize::SZ - 2, usize::SZ - 2);

    group.bench_function("noop", |c| {
        c.iter(|| {
            let _ = black_box(Layout::aligned_alloc_compatible_from_size_align(
                black_box(noop.0),
                black_box(noop.1)
            ));
        });
    });

    group.bench_function("round_size", |c| {
        c.iter(|| {
            let _ = black_box(Layout::aligned_alloc_compatible_from_size_align(
                black_box(round_size.0),
                black_box(round_size.1)
            ));
        });
    });

    group.bench_function("round_align", |c| {
        c.iter(|| {
            let _ = black_box(Layout::aligned_alloc_compatible_from_size_align(
                black_box(round_align.0),
                black_box(round_align.1)
            ));
        });
    });

    group.bench_function("round_both", |c| {
        c.iter(|| {
            let _ = black_box(Layout::aligned_alloc_compatible_from_size_align(
                black_box(round_both.0),
                black_box(round_both.1)
            ));
        });
    });
}

fn array(c: &mut Criterion) {
    let mut group = c.benchmark_group("array");

    let sizes = [1024, 2048, 729, 2187];

    for sz in sizes {
        group.bench_function(&format!("{}_u8", sz), |c| {
            c.iter(|| {
                let _ = black_box(Layout::array::<u8>(black_box(black_box(sz))));
            });
        });

        group.bench_function(&format!("{}_u32", sz), |c| {
            c.iter(|| {
                let _ = black_box(Layout::array::<u32>(black_box(black_box(sz))));
            });
        });

        group.bench_function(&format!("{}_u64", sz), |c| {
            c.iter(|| {
                let _ = black_box(Layout::array::<u64>(black_box(black_box(sz))));
            });
        });
    }
}

fn repeat(c: &mut Criterion) {
    let mut group = c.benchmark_group("array");

    let u8 = u8::LAYOUT;
    let u32 = u32::LAYOUT;
    let u64 = u64::LAYOUT;

    let sizes = [1024, 2048, 729, 2187];

    for sz in sizes {
        group.bench_function(&format!("{}_u8", sz), |c| {
            c.iter(|| {
                let _ = black_box(black_box(u8).repeat(black_box(sz)));
            });
        });

        group.bench_function(&format!("{}_u32", sz), |c| {
            c.iter(|| {
                let _ = black_box(black_box(u32).repeat(black_box(sz)));
            });
        });

        group.bench_function(&format!("{}_u64", sz), |c| {
            c.iter(|| {
                let _ = black_box(black_box(u64).repeat(black_box(sz)));
            });
        });
    }
}

fn repeat_packed(c: &mut Criterion) {
    let mut group = c.benchmark_group("array");

    let u8 = u8::LAYOUT;
    let u32 = u32::LAYOUT;
    let u64 = u64::LAYOUT;

    let sizes = [1024, 2048, 729, 2187];

    for sz in sizes {
        group.bench_function(&format!("{}_u8", sz), |c| {
            c.iter(|| {
                let _ = black_box(black_box(u8).repeat_packed(black_box(sz)));
            });
        });

        group.bench_function(&format!("{}_u32", sz), |c| {
            c.iter(|| {
                let _ = black_box(black_box(u32).repeat_packed(black_box(sz)));
            });
        });

        group.bench_function(&format!("{}_u64", sz), |c| {
            c.iter(|| {
                let _ = black_box(black_box(u64).repeat_packed(black_box(sz)));
            });
        });
    }
}

fn main() {
    let mut c = Criterion::default()
        .sample_size(512)
        .nresamples(200_000)
        .confidence_level(0.99)
        .configure_from_args();

    to_aligned_alloc_compatible(&mut c);
    aligned_alloc_compatible_from_size_align(&mut c);
    array(&mut c);
    repeat(&mut c);
    repeat_packed(&mut c);

    c.final_summary();
}
