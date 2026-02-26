#![allow(clippy::incompatible_msrv)]

extern crate criterion;
extern crate memapi2;

use {
    core::hint::black_box,
    criterion::Criterion,
    memapi2::{
        helpers::USIZE_MAX_NO_HIGH_BIT,
        layout::Layout,
        traits::data::type_props::SizedProps
    },
    std::time::Duration
};

fn to_posix_memalign_compatible(c: &mut Criterion) {
    // i'm not lazy wdym
    let mut group = c.benchmark_group("taac");

    let noop = unsafe { Layout::from_size_align_unchecked(usize::SZ, usize::ALN) };
    let round_size = unsafe { Layout::from_size_align_unchecked(usize::SZ - 2, usize::ALN) };
    let round_align = unsafe { Layout::from_size_align_unchecked(usize::SZ, usize::ALN - 2) };
    let round_both = unsafe { Layout::from_size_align_unchecked(usize::SZ - 2, usize::ALN - 2) };

    group.bench_function("noop", |c| {
        c.iter(|| {
            let _ = black_box(black_box(noop).to_posix_memalign_compatible());
        });
    });

    group.bench_function("round_size", |c| {
        c.iter(|| {
            let _ = black_box(black_box(round_size).to_posix_memalign_compatible());
        });
    });

    group.bench_function("round_align", |c| {
        c.iter(|| {
            let _ = black_box(black_box(round_align).to_posix_memalign_compatible());
        });
    });

    group.bench_function("round_both", |c| {
        c.iter(|| {
            let _ = black_box(black_box(round_both).to_posix_memalign_compatible());
        });
    });

    group.finish();
}

fn posix_memalign_compatible_from_size_align(c: &mut Criterion) {
    let mut group = c.benchmark_group("aacfsa");

    let noop = (usize::SZ, usize::ALN);
    let round_size = (usize::SZ - 2, usize::ALN);
    let round_align = (usize::SZ, usize::SZ - 2);
    let round_both = (usize::SZ - 2, usize::SZ - 2);

    group.bench_function("noop", |c| {
        c.iter(|| {
            let _ = black_box(Layout::posix_memalign_compatible_from_size_align(
                black_box(noop.0),
                black_box(noop.1)
            ));
        });
    });

    group.bench_function("round_size", |c| {
        c.iter(|| {
            let _ = black_box(Layout::posix_memalign_compatible_from_size_align(
                black_box(round_size.0),
                black_box(round_size.1)
            ));
        });
    });

    group.bench_function("round_align", |c| {
        c.iter(|| {
            let _ = black_box(Layout::posix_memalign_compatible_from_size_align(
                black_box(round_align.0),
                black_box(round_align.1)
            ));
        });
    });

    group.bench_function("round_both", |c| {
        c.iter(|| {
            let _ = black_box(Layout::posix_memalign_compatible_from_size_align(
                black_box(round_both.0),
                black_box(round_both.1)
            ));
        });
    });

    group.finish();
}

fn array(c: &mut Criterion) {
    let mut group = c.benchmark_group("array");

    group.bench_function("1024_u8", |c| {
        c.iter(|| {
            let _ = black_box(Layout::array::<u8>(black_box(black_box(1024))));
        });
    });

    group.bench_function("1024_u32", |c| {
        c.iter(|| {
            let _ = black_box(Layout::array::<u32>(black_box(black_box(1024))));
        });
    });

    group.bench_function("1024_u64", |c| {
        c.iter(|| {
            let _ = black_box(Layout::array::<u64>(black_box(black_box(1024))));
        });
    });

    group.finish();
}

fn repeat(c: &mut Criterion) {
    let mut group = c.benchmark_group("array");

    let u8 = u8::LAYOUT;
    let u32 = u32::LAYOUT;
    let u64 = u64::LAYOUT;

    group.bench_function("1024_u8", |c| {
        c.iter(|| {
            let _ = black_box(black_box(u8).repeat(black_box(1024)));
        });
    });

    group.bench_function("1024_u32", |c| {
        c.iter(|| {
            let _ = black_box(black_box(u32).repeat(black_box(1024)));
        });
    });

    group.bench_function("1024_u64", |c| {
        c.iter(|| {
            let _ = black_box(black_box(u64).repeat(black_box(1024)));
        });
    });

    group.finish();
}

fn repeat_packed(c: &mut Criterion) {
    let mut group = c.benchmark_group("array");

    let u8 = u8::LAYOUT;
    let u32 = u32::LAYOUT;
    let u64 = u64::LAYOUT;

    group.bench_function("1024_u8", |c| {
        c.iter(|| {
            let _ = black_box(black_box(u8).repeat_packed(black_box(1024)));
        });
    });

    group.bench_function("1024_u32", |c| {
        c.iter(|| {
            let _ = black_box(black_box(u32).repeat_packed(black_box(1024)));
        });
    });

    group.bench_function("1024_u64", |c| {
        c.iter(|| {
            let _ = black_box(black_box(u64).repeat_packed(black_box(1024)));
        });
    });

    group.finish();
}

fn from_size_align(c: &mut Criterion) {
    let mut group = c.benchmark_group("fsa");

    let valid: (usize, usize) = (usize::SZ, usize::ALN);
    let nonpow2: (usize, usize) = (usize::SZ, usize::ALN - 1);
    let zero: (usize, usize) = (usize::SZ, 0);
    let too_big: (usize, usize) = (USIZE_MAX_NO_HIGH_BIT, 2);

    group.bench_function("valid", |c| {
        c.iter(|| {
            let _ = black_box(Layout::from_size_align(black_box(valid.0), black_box(valid.1)));
        });
    });

    group.bench_function("nonpow2", |c| {
        c.iter(|| {
            let _ = black_box(Layout::from_size_align(black_box(nonpow2.0), black_box(nonpow2.1)));
        });
    });

    group.bench_function("zero", |c| {
        c.iter(|| {
            let _ = black_box(Layout::from_size_align(black_box(zero.0), black_box(zero.1)));
        });
    });

    group.bench_function("too_big", |c| {
        c.iter(|| {
            let _ = black_box(Layout::from_size_align(black_box(too_big.0), black_box(too_big.1)));
        });
    });

    group.bench_function("valid_unchecked", |c| {
        c.iter(|| {
            let _ = black_box(unsafe {
                Layout::from_size_align_unchecked(black_box(valid.0), black_box(valid.1))
            });
        });
    });

    group.finish();
}

fn main() {
    let mut c = Criterion::default()
        .sample_size(512)
        .measurement_time(Duration::from_secs(8))
        .nresamples(200_000)
        .noise_threshold(0.005)
        .confidence_level(0.99)
        .significance_level(0.1)
        .configure_from_args();

    to_posix_memalign_compatible(&mut c);
    posix_memalign_compatible_from_size_align(&mut c);
    array(&mut c);
    repeat(&mut c);
    repeat_packed(&mut c);
    from_size_align(&mut c);

    c.final_summary();
}
