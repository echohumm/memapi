extern crate criterion;
extern crate memapi2;

use {
    core::hint::black_box,
    criterion::Criterion,
    memapi2::{Layout, data::type_props::SizedProps},
    std::time::Duration
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

fn main() {
    let mut c = Criterion::default()
        .measurement_time(Duration::from_millis(5_000))
        .confidence_level(0.99)
        .noise_threshold(0.02)
        .nresamples(500_000)
        .sample_size(1000)
        .configure_from_args();

    to_aligned_alloc_compatible(&mut c);
    aligned_alloc_compatible_from_size_align(&mut c);

    c.final_summary();
}
