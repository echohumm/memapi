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
        helpers::{null_q, null_q_dyn},
        layout::Layout,
        traits::data::type_props::PtrProps
    },
    std::{rc::Rc, sync::Arc, time::Duration}
};

fn null_q_variants(c: &mut Criterion) {
    let mut group = c.benchmark_group("null_q");

    let invalid_ptr: *mut u8 = null_mut();
    let valid_ptr: *mut u8 = dangling_mut();

    let layout = Layout::new::<usize>();

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
}

fn ptr_props(c: &mut Criterion) {
    macro_rules! benches {
        ($c:ident. $($v:ident),*) => {
            $(
                let mut group = $c.benchmark_group(concat!("ptr_props/", stringify!($v)));
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

    let refer = dummy.as_str();
    let immut_ptr = refer as *const str;
    let mut_ptr = immut_ptr as *mut str;
    let nonnull = NonNull::new(mut_ptr).unwrap();

    let boxed: Box<str> = Box::from(dummy.as_str());
    let arc: Arc<str> = Arc::from(dummy.as_str());
    let rc: Rc<str> = Rc::from(dummy.as_str());

    benches! { c. refer, immut_ptr, mut_ptr, nonnull, boxed, arc, rc }
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

    null_q_variants(&mut c);
    ptr_props(&mut c);

    c.final_summary();
}
