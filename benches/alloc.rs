#![allow(clippy::incompatible_msrv)]

extern crate criterion;
extern crate memapi2;

use {
    core::{hint::black_box, ptr::NonNull},
    criterion::Criterion,
    memapi2::{
        DefaultAlloc,
        layout::Layout,
        traits::alloc::{Alloc, Dealloc, Grow, Realloc, Shrink}
    }
};

fn bench_allocs<A>(c: &mut Criterion, name: &str, alloc: A)
where
    A: Alloc + Dealloc + Grow + Shrink + Realloc
{
    let mut group = c.benchmark_group(name);
    let zero = unsafe { Layout::from_size_align_unchecked(0, 8) };
    let small = unsafe { Layout::from_size_align_unchecked(32, 8) };
    let large = unsafe { Layout::from_size_align_unchecked(64, 8) };

    group.bench_function("alloc", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.alloc(black_box(l)).unwrap();
            unsafe { alloc.dealloc(black_box(ptr), black_box(l)) };
        });
    });

    group.bench_function("zalloc", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.zalloc(black_box(l)).unwrap();
            unsafe { alloc.dealloc(black_box(ptr), black_box(l)) };
        });
    });

    group.bench_function("dealloc", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.alloc(black_box(l)).unwrap();
            unsafe { alloc.dealloc(black_box(ptr), black_box(l)) };
        });
    });

    group.bench_function("try_dealloc", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.alloc(black_box(l)).unwrap();
            unsafe { alloc.try_dealloc(black_box(ptr), black_box(l)).unwrap() };
        });
    });

    group.bench_function("grow", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc(black_box(old_l)).unwrap();
            let new_ptr = alloc.grow(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("zgrow", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc(black_box(old_l)).unwrap();
            let new_ptr = alloc.zgrow(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("shrink", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(large);
            let new_l = black_box(small);
            let ptr = alloc.alloc(black_box(old_l)).unwrap();
            let new_ptr = alloc.shrink(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("realloc", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.realloc(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("rezalloc", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.rezalloc(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("realloc_oldzsl_dangling", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(zero);
            let new_l = black_box(large);
            let ptr = NonNull::dangling();
            let new_ptr =
                alloc.realloc(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        })
    });

    group.bench_function("rezalloc_oldzsl_dangling", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(zero);
            let new_l = black_box(large);
            let ptr = NonNull::dangling();
            let new_ptr =
                alloc.rezalloc(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc(black_box(new_ptr), black_box(new_l));
        })
    });

    group.finish();
}

fn bench_allocs_mut<A>(c: &mut Criterion, name: &str, alloc: A)
where
    A: memapi2::traits::alloc_mut::FullAllocMut + Copy
{
    let mut alloc = alloc;

    let mut group = c.benchmark_group(name);
    let zero = unsafe { Layout::from_size_align_unchecked(0, 8) };
    let small = unsafe { Layout::from_size_align_unchecked(32, 8) };
    let large = unsafe { Layout::from_size_align_unchecked(64, 8) };

    group.bench_function("alloc_mut", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.alloc_mut(black_box(l)).unwrap();
            unsafe { alloc.dealloc_mut(black_box(ptr), black_box(l)) };
        });
    });

    group.bench_function("zalloc_mut", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.zalloc_mut(black_box(l)).unwrap();
            unsafe { alloc.dealloc_mut(black_box(ptr), black_box(l)) };
        });
    });

    group.bench_function("dealloc_mut", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.alloc_mut(black_box(l)).unwrap();
            unsafe { alloc.dealloc_mut(black_box(ptr), black_box(l)) };
        });
    });

    group.bench_function("try_dealloc_mut", |b| {
        b.iter(|| {
            let l = black_box(small);
            let ptr = alloc.alloc_mut(black_box(l)).unwrap();
            unsafe { alloc.try_dealloc_mut(black_box(ptr), black_box(l)).unwrap() };
        });
    });

    group.bench_function("grow_mut", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc_mut(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.grow_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("zgrow_mut", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc_mut(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.zgrow_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("shrink_mut", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(large);
            let new_l = black_box(small);
            let ptr = alloc.alloc_mut(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.shrink_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("realloc_mut", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc_mut(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.realloc_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("rezalloc_mut", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = alloc.alloc_mut(black_box(old_l)).unwrap();
            let new_ptr =
                alloc.rezalloc_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        });
    });

    group.bench_function("realloc_oldzsl_dangling", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(zero);
            let new_l = black_box(large);
            let ptr = NonNull::dangling();
            let new_ptr =
                alloc.realloc_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        })
    });

    group.bench_function("rezalloc_oldzsl_dangling", |b| {
        b.iter(|| unsafe {
            let old_l = black_box(zero);
            let new_l = black_box(large);
            let ptr = NonNull::dangling();
            let new_ptr =
                alloc.rezalloc_mut(black_box(ptr), black_box(old_l), black_box(new_l)).unwrap();
            alloc.dealloc_mut(black_box(new_ptr), black_box(new_l));
        })
    });

    group.finish();
}

#[cfg(feature = "alloc_temp_trait")]
fn bench_allocs_temp<A>(c: &mut Criterion, name: &str, alloc: A)
where
    A: memapi2::traits::alloc_temp::AllocTemp + Copy
{
    let mut group = c.benchmark_group(name);
    let small = unsafe { Layout::from_size_align_unchecked(32, 8) };

    group.bench_function("alloc_temp", |b| {
        b.iter(|| unsafe {
            let l = black_box(small);
            let _ = alloc.alloc_temp(black_box(l), |ptr| black_box(ptr)).unwrap();
        });
    });

    group.bench_function("zalloc_temp", |b| {
        b.iter(|| unsafe {
            let l = black_box(small);
            let _ = alloc.zalloc_temp(black_box(l), |ptr| black_box(ptr)).unwrap();
        });
    });

    group.finish();
}

fn main() {
    let mut c = Criterion::default()
        .sample_size(512)
        .nresamples(200_000)
        .noise_threshold(0.005)
        .confidence_level(0.99)
        .configure_from_args();

    bench_allocs(&mut c, "default_alloc", DefaultAlloc);
    #[cfg(feature = "c_alloc")]
    bench_allocs(&mut c, "c_alloc", memapi2::allocs::c_alloc::CAlloc);

    bench_allocs_mut(&mut c, "default_alloc", DefaultAlloc);
    #[cfg(feature = "c_alloc")]
    bench_allocs_mut(&mut c, "c_alloc", memapi2::allocs::c_alloc::CAlloc);

    #[cfg(feature = "std")]
    bench_allocs(&mut c, "default_alloc_wrapped", std::sync::Mutex::new(DefaultAlloc));

    #[cfg(feature = "alloc_temp_trait")]
    {
        bench_allocs_temp(&mut c, "default_alloc", DefaultAlloc);
        #[cfg(feature = "c_alloc")]
        bench_allocs_temp(&mut c, "c_alloc", memapi2::allocs::c_alloc::CAlloc);
        #[cfg(feature = "stack_alloc")]
        bench_allocs_temp(&mut c, "stack_alloc", memapi2::allocs::stack_alloc::StackAlloc);
    }

    c.final_summary();
}
