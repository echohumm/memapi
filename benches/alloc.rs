#![allow(clippy::incompatible_msrv)]

extern crate criterion;
extern crate memapi2;

use {
    ::core::hint::black_box,
    criterion::Criterion,
    memapi2::{
        DefaultAlloc,
        layout::Layout,
        traits::alloc::{Alloc, Dealloc, Grow, Realloc, Shrink}
    }
};

fn bench_allocs<A>(c: &mut Criterion, name: &str, alloc: A)
where
    A: Alloc + Dealloc + Grow + Shrink + Realloc + Copy
{
    let mut group = c.benchmark_group(name);
    let small = unsafe { Layout::from_size_align_unchecked(32, 8) };
    let large = unsafe { Layout::from_size_align_unchecked(64, 8) };

    group.bench_function("alloc", |b| {
        b.iter(|| {
            let a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.alloc(l).unwrap();
            unsafe { a.dealloc(ptr, l) };
        });
    });

    group.bench_function("zalloc", |b| {
        b.iter(|| {
            let a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.zalloc(l).unwrap();
            unsafe { a.dealloc(ptr, l) };
        });
    });

    group.bench_function("dealloc", |b| {
        b.iter(|| {
            let a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.alloc(l).unwrap();
            unsafe { a.dealloc(ptr, l) };
        });
    });

    group.bench_function("try_dealloc", |b| {
        b.iter(|| {
            let a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.alloc(l).unwrap();
            unsafe { a.try_dealloc(ptr, l).unwrap() };
        });
    });

    group.bench_function("grow", |b| {
        b.iter(|| unsafe {
            let a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc(old_l).unwrap();
            let new_ptr = a.grow(ptr, old_l, new_l).unwrap();
            a.dealloc(new_ptr, new_l);
        });
    });

    group.bench_function("zgrow", |b| {
        b.iter(|| unsafe {
            let a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc(old_l).unwrap();
            let new_ptr = a.zgrow(ptr, old_l, new_l).unwrap();
            a.dealloc(new_ptr, new_l);
        });
    });

    group.bench_function("shrink", |b| {
        b.iter(|| unsafe {
            let a = black_box(alloc);
            let old_l = black_box(large);
            let new_l = black_box(small);
            let ptr = a.alloc(old_l).unwrap();
            let new_ptr = a.shrink(ptr, old_l, new_l).unwrap();
            a.dealloc(new_ptr, new_l);
        });
    });

    group.bench_function("realloc", |b| {
        b.iter(|| unsafe {
            let a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc(old_l).unwrap();
            let new_ptr = a.realloc(ptr, old_l, new_l).unwrap();
            a.dealloc(new_ptr, new_l);
        });
    });

    group.bench_function("rezalloc", |b| {
        b.iter(|| unsafe {
            let a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc(old_l).unwrap();
            let new_ptr = a.rezalloc(ptr, old_l, new_l).unwrap();
            a.dealloc(new_ptr, new_l);
        });
    });

    group.finish();
}

fn bench_allocs_mut<A>(c: &mut Criterion, name: &str, alloc: A)
where
    A: memapi2::traits::alloc_mut::FullAllocMut + Copy
{
    let mut group = c.benchmark_group(name);
    let small = unsafe { Layout::from_size_align_unchecked(32, 8) };
    let large = unsafe { Layout::from_size_align_unchecked(64, 8) };

    group.bench_function("alloc_mut", |b| {
        b.iter(|| {
            let mut a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.alloc_mut(l).unwrap();
            unsafe { a.dealloc_mut(ptr, l) };
        });
    });

    group.bench_function("zalloc_mut", |b| {
        b.iter(|| {
            let mut a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.zalloc_mut(l).unwrap();
            unsafe { a.dealloc_mut(ptr, l) };
        });
    });

    group.bench_function("dealloc_mut", |b| {
        b.iter(|| {
            let mut a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.alloc_mut(l).unwrap();
            unsafe { a.dealloc_mut(ptr, l) };
        });
    });

    group.bench_function("try_dealloc_mut", |b| {
        b.iter(|| {
            let mut a = black_box(alloc);
            let l = black_box(small);
            let ptr = a.alloc_mut(l).unwrap();
            unsafe { a.try_dealloc_mut(ptr, l).unwrap() };
        });
    });

    group.bench_function("grow_mut", |b| {
        b.iter(|| unsafe {
            let mut a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc_mut(old_l).unwrap();
            let new_ptr = a.grow_mut(ptr, old_l, new_l).unwrap();
            a.dealloc_mut(new_ptr, new_l);
        });
    });

    group.bench_function("zgrow_mut", |b| {
        b.iter(|| unsafe {
            let mut a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc_mut(old_l).unwrap();
            let new_ptr = a.zgrow_mut(ptr, old_l, new_l).unwrap();
            a.dealloc_mut(new_ptr, new_l);
        });
    });

    group.bench_function("shrink_mut", |b| {
        b.iter(|| unsafe {
            let mut a = black_box(alloc);
            let old_l = black_box(large);
            let new_l = black_box(small);
            let ptr = a.alloc_mut(old_l).unwrap();
            let new_ptr = a.shrink_mut(ptr, old_l, new_l).unwrap();
            a.dealloc_mut(new_ptr, new_l);
        });
    });

    group.bench_function("realloc_mut", |b| {
        b.iter(|| unsafe {
            let mut a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc_mut(old_l).unwrap();
            let new_ptr = a.realloc_mut(ptr, old_l, new_l).unwrap();
            a.dealloc_mut(new_ptr, new_l);
        });
    });

    group.bench_function("rezalloc_mut", |b| {
        b.iter(|| unsafe {
            let mut a = black_box(alloc);
            let old_l = black_box(small);
            let new_l = black_box(large);
            let ptr = a.alloc_mut(old_l).unwrap();
            let new_ptr = a.rezalloc_mut(ptr, old_l, new_l).unwrap();
            a.dealloc_mut(new_ptr, new_l);
        });
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
            let a = black_box(alloc);
            let l = black_box(small);
            let _ = a.alloc_temp(l, |ptr| black_box(ptr)).unwrap();
        });
    });

    group.bench_function("zalloc_temp", |b| {
        b.iter(|| unsafe {
            let a = black_box(alloc);
            let l = black_box(small);
            let _ = a.zalloc_temp(l, |ptr| black_box(ptr)).unwrap();
        });
    });

    group.finish();
}

fn main() {
    let mut c = Criterion::default()
        .sample_size(512)
        .nresamples(200_000)
        .confidence_level(0.99)
        .configure_from_args();

    bench_allocs(&mut c, "default_alloc", DefaultAlloc);
    #[cfg(feature = "c_alloc")]
    bench_allocs(&mut c, "c_alloc", memapi2::allocs::c_alloc::CAlloc);

    bench_allocs_mut(&mut c, "default_alloc_mut", DefaultAlloc);
    #[cfg(feature = "c_alloc")]
    bench_allocs_mut(&mut c, "c_alloc_mut", memapi2::allocs::c_alloc::CAlloc);

    #[cfg(feature = "alloc_temp_trait")]
    {
        bench_allocs_temp(&mut c, "default_alloc_temp", DefaultAlloc);
        #[cfg(feature = "c_alloc")]
        bench_allocs_temp(&mut c, "c_alloc_temp", memapi2::allocs::c_alloc::CAlloc);
        #[cfg(feature = "stack_alloc")]
        bench_allocs_temp(&mut c, "stack_alloc_temp", memapi2::allocs::stack_alloc::StackAlloc);
    }

    c.final_summary();
}
