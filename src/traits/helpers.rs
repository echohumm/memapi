use {
    crate::{error::Error, layout::Layout, prelude::DeallocMut, traits::alloc::Dealloc},
    ::core::{
        cmp::{Ord, Ordering, min},
        convert::From,
        fmt::{Debug, Display},
        hint::unreachable_unchecked,
        marker::Sized,
        option::Option::{self},
        panic,
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok}
    }
};

pub fn default_dealloc_panic<E: Display>(ptr: NonNull<u8>, layout: Layout, e: E) -> ! {
    panic!("deallocation of block at {:p} with layout {:?} failed: {}", ptr.as_ptr(), layout, e)
}

//noinspection DuplicatedCode
#[cfg_attr(miri, track_caller)]
pub unsafe fn ralloc<A: Dealloc<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
    a: &A,
    ptr: NonNull<u8>,
    old: Layout,
    new: Layout,
    alloc: fn(&A, Layout) -> Result<NonNull<u8>, E>,
    less: Option<fn(usize, usize) -> Error>,
    greater: Option<fn(usize, usize) -> Error>
) -> Result<NonNull<u8>, E> {
    let old_align = old.align();
    let new_align = new.align();

    if new_align < old_align {
        return Err(E::from(Error::ReallocSmallerAlign(old_align, new_align)));
    }

    let old_size = old.size();
    let new_size = new.size();

    let new_ptr = match new_size.cmp(&old_size) {
        Ordering::Greater => greater
            .map_or_else(|| alloc(a, new), |greater| Err(E::from(greater(old_size, new_size)))),
        Ordering::Equal => {
            match new_align.cmp(&old_align) {
                Ordering::Greater => alloc(a, new),
                Ordering::Equal => Ok(ptr),
                // SAFETY: we check above that new_align >= old_align
                Ordering::Less => unsafe { unreachable_unchecked() }
            }
        }
        Ordering::Less => {
            less.map_or_else(|| alloc(a, new), |less| Err(E::from(less(old_size, new_size))))
        }
    };
    if let Ok(new_ptr) = new_ptr {
        // for some reason, the dealloc call being outside of this branch is faster (for most
        // things)? idk
        if old_size > 0 {
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), min(old_size, new_size));
        }

        tri!(do a.try_dealloc(ptr, old));
    }
    new_ptr
}

#[cfg_attr(miri, track_caller)]
pub unsafe fn ralloc_mut<A: DeallocMut<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
    a: &mut A,
    ptr: NonNull<u8>,
    old: Layout,
    new: Layout,
    alloc: fn(&mut A, Layout) -> Result<NonNull<u8>, E>,
    less: Option<fn(usize, usize) -> Error>,
    greater: Option<fn(usize, usize) -> Error>
) -> Result<NonNull<u8>, E> {
    let old_align = old.align();
    let new_align = new.align();

    if new_align < old_align {
        return Err(E::from(Error::ReallocSmallerAlign(old_align, new_align)));
    }

    let old_size = old.size();
    let new_size = new.size();

    let new_ptr = match new_size.cmp(&old_size) {
        Ordering::Greater => greater
            .map_or_else(|| alloc(a, new), |greater| Err(E::from(greater(old_size, new_size)))),
        Ordering::Equal => {
            match new_align.cmp(&old_align) {
                Ordering::Greater => alloc(a, new),
                Ordering::Equal => Ok(ptr),
                // SAFETY: we checked above that new_align >= old_align
                Ordering::Less => unsafe { unreachable_unchecked() }
            }
        }
        Ordering::Less => {
            less.map_or_else(|| alloc(a, new), |less| Err(E::from(less(old_size, new_size))))
        }
    };
    if let Ok(new_ptr) = new_ptr {
        if old_size > 0 {
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), min(old_size, new_size));
        }

        tri!(do a.try_dealloc_mut(ptr, old));
    }
    new_ptr
}
