#![allow(clippy::incompatible_msrv)]

extern crate criterion;
extern crate memapi2;

use {
    core::{
        hint::black_box,
        ptr::{dangling_mut, null_mut}
    },
    criterion::Criterion,
    memapi2::{
        error::ArithOp,
        helpers::{checked_op, null_q, null_q_dyn, null_q_dyn_zsl_check},
        layout::Layout
    }
};

fn checked_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("checked_ops/add");

    group.bench_function("valid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Add, black_box(2)));
        });
    });

    group.bench_function("invalid", |b| {
        b.iter(|| {
            // overflows
            let _ = black_box(checked_op(black_box(usize::MAX), ArithOp::Add, black_box(1)));
        });
    });

    group.finish();

    let mut group = c.benchmark_group("checked_ops/sub");

    group.bench_function("valid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Sub, black_box(2)));
        });
    });

    group.bench_function("invalid", |b| {
        b.iter(|| {
            // underflows
            let _ = black_box(checked_op(black_box(0), ArithOp::Sub, black_box(1)));
        });
    });

    group.finish();

    let mut group = c.benchmark_group("checked_ops/mul");

    group.bench_function("valid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Mul, black_box(2)));
        });
    });

    group.bench_function("invalid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(usize::MAX), ArithOp::Mul, black_box(2)));
        });
    });

    group.finish();

    let mut group = c.benchmark_group("checked_ops/div");

    group.bench_function("valid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Div, black_box(2)));
        });
    });

    group.bench_function("valid_rem", |b| {
        b.iter(|| {
            // has a remainder of 1
            let _ = black_box(checked_op(black_box(3), ArithOp::Div, black_box(2)));
        });
    });

    group.bench_function("valid_toolarge", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Div, black_box(3)));
        });
    });

    group.bench_function("invalid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Div, black_box(0)));
        });
    });

    group.finish();

    let mut group = c.benchmark_group("checked_ops/rem");

    group.bench_function("valid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(3), ArithOp::Rem, black_box(2)));
        });
    });

    group.bench_function("valid_exact", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Rem, black_box(2)));
        });
    });

    group.bench_function("valid_toolarge", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Rem, black_box(3)));
        });
    });

    group.bench_function("invalid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Rem, black_box(0)));
        });
    });

    group.finish();

    let mut group = c.benchmark_group("checked_ops/pow");

    group.bench_function("valid_0", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Pow, black_box(0)));
        });
    });

    group.bench_function("valid", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Pow, black_box(1)));
        });
    });

    group.bench_function("valid_long", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(1), ArithOp::Pow, black_box(u32::MAX as usize)));
        });
    });

    group.bench_function("invalid_toolarge", |b| {
        b.iter(|| {
            let _ =
                black_box(checked_op(black_box(2), ArithOp::Pow, black_box(u32::MAX as usize + 1)));
        });
    });

    group.bench_function("invalid_overflow_long", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(2), ArithOp::Pow, black_box(64)));
        });
    });

    group.bench_function("invalid_overflow_short", |b| {
        b.iter(|| {
            let _ = black_box(checked_op(black_box(usize::MAX), ArithOp::Pow, black_box(2)));
        });
    });

    group.finish();
}

fn null_q_variants(c: &mut Criterion) {
    let mut group = c.benchmark_group("null_q");

    let invalid_ptr: *mut u8 = null_mut();
    let valid_ptr: *mut u8 = dangling_mut();

    let layout = Layout::new::<usize>();
    let zsl_layout = Layout::from_size_align(0, 1).unwrap();

    group.bench_function("null_q_valid", |b| {
        b.iter(|| black_box(null_q(black_box(valid_ptr), black_box(layout))))
    });
    group.bench_function("null_q_invalid", |b| {
        b.iter(|| black_box(null_q(black_box(invalid_ptr), black_box(layout))))
    });

    group.bench_function("null_q_dyn_valid", |b| {
        b.iter(|| black_box(null_q_dyn(black_box(valid_ptr), black_box(layout))))
    });
    group.bench_function("null_q_dyn_invalid", |b| {
        b.iter(|| black_box(null_q_dyn(black_box(invalid_ptr), black_box(layout))))
    });

    group.bench_function("null_q_dyn_zsl_check_valid", |b| {
        b.iter(|| {
            let _ = black_box(null_q_dyn_zsl_check(
                black_box(layout),
                black_box(|l| {
                    black_box(l);
                    black_box(valid_ptr)
                })
            ));
        });
    });
    group.bench_function("null_q_dyn_zsl_check_invalid_ptr", |b| {
        b.iter(|| {
            let _ = black_box(null_q_dyn_zsl_check(
                black_box(layout),
                black_box(|l| {
                    black_box(l);
                    black_box(invalid_ptr)
                })
            ));
        });
    });
    group.bench_function("null_q_dyn_zsl_check_invalid_layout", |b| {
        b.iter(|| {
            let _ = black_box(null_q_dyn_zsl_check(
                black_box(zsl_layout),
                black_box(|l| {
                    black_box(l);
                    black_box(valid_ptr)
                })
            ));
        });
    });
    group.bench_function("null_q_dyn_zsl_check_invalid", |b| {
        b.iter(|| {
            let _ = black_box(null_q_dyn_zsl_check(
                black_box(zsl_layout),
                black_box(|l| {
                    black_box(l);
                    black_box(invalid_ptr)
                })
            ));
        });
    });
}

fn main() {
    let mut c = Criterion::default()
        .sample_size(512)
        .nresamples(200_000)
        .confidence_level(0.99)
        .configure_from_args();

    checked_ops(&mut c);
    null_q_variants(&mut c);

    c.final_summary();
}
