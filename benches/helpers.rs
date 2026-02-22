#![allow(clippy::incompatible_msrv)]

extern crate criterion;
extern crate memapi2;

use {
    core::{
        hint::black_box,
        ptr::{NonNull, dangling_mut, null_mut}
    },
    criterion::Criterion,
    memapi2::{
        error::ArithOp,
        helpers::{checked_op, null_q, null_q_dyn, null_q_dyn_zsl_check},
        layout::Layout,
        traits::data::type_props::PtrProps
    },
    std::{rc::Rc, sync::Arc}
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

fn ptr_props(c: &mut Criterion) {
    macro_rules! benches {
        ($($v:ident),*) => {
            $(
                let mut group = c.benchmark_group(concat!("ptr_props/", stringify!($v)));
                group.bench_function("sz", |b| {
                    b.iter(|| {
                        let _ = black_box(unsafe { $v.sz() });
                    });
                });
                group.bench_function("aln", |b| {
                    b.iter(|| {
                        let _ = black_box(unsafe { $v.aln() });
                    });
                });
                group.bench_function("layout", |b| {
                    b.iter(|| {
                        let _ = black_box(unsafe { $v.layout() });
                    });
                });
                group.bench_function("is_zst", |b| {
                    b.iter(|| {
                        let _ = black_box(unsafe { $v.is_zero_sized() });
                    });
                });
                group.bench_function("max_slice_len", |b| {
                    b.iter(|| {
                        let _ = black_box(unsafe { $v.max_slice_len() });
                    });
                });
                #[cfg(feature = "metadata")]
                group.bench_function("metadata", |b| {
                    b.iter(|| {
                        let _ = black_box(unsafe { $v.metadata() });
                    });
                });
                group.bench_function("varsized_metadata", |b| {
                    b.iter(|| {
                        let _ = black_box($v.varsized_metadata());
                    });
                });
                group.finish();
            )*
        };
    }
    let dummy = "string".to_string();

    let r = dummy.as_str();
    let p = r as *const str;
    let mp = p as *mut str;
    let nn = NonNull::new(mp).unwrap();

    let boxed_dummy: Box<str> = Box::from(dummy.as_str());
    let arc_dummy: Arc<str> = Arc::from(dummy.as_str());
    let rc_dummy: Rc<str> = Rc::from(dummy.as_str());

    benches! { r, p, mp, nn, boxed_dummy, arc_dummy, rc_dummy }
}

fn main() {
    let mut c = Criterion::default()
        .sample_size(512)
        .nresamples(200_000)
        .noise_threshold(0.005)
        .confidence_level(0.99)
        .configure_from_args();

    checked_ops(&mut c);
    null_q_variants(&mut c);
    ptr_props(&mut c);

    c.final_summary();
}
