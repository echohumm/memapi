use {
    crate::{error::Error, layout::Layout, traits::alloc::Dealloc},
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
    less: Option<E>,
    greater: Option<E>
) -> Result<NonNull<u8>, E> {
    let old_align = old.align();
    let new_align = new.align();

    if new_align < old_align {
        return Err(E::from(Error::ReallocSmallerAlign(old_align, new_align)));
    }

    let old_size = old.size();
    let new_size = new.size();

    let new_ptr = match new_size.cmp(&old_size) {
        Ordering::Greater => greater.map_or_else(|| alloc(a, new), |greater| Err(greater)),
        Ordering::Equal => {
            match new_align.cmp(&old_align) {
                Ordering::Greater => alloc(a, new),
                Ordering::Equal => Ok(ptr),
                // SAFETY: we check above that new_align >= old_align
                Ordering::Less => unsafe { unreachable_unchecked() }
            }
        }
        Ordering::Less => less.map_or_else(|| alloc(a, new), |less| Err(less))
    };
    if let Ok(new_ptr) = new_ptr {
        if old_size > 0 {
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), min(old_size, new_size));
            tri!(do a.try_dealloc(ptr, old));
        }
    }
    new_ptr
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Bytes {
    Uninitialized,
    Zeroed
}

pub mod alloc_mut {
    use {
        crate::{
            error::Error,
            layout::Layout,
            traits::{
                alloc_mut::{GrowMut, ReallocMut, ShrinkMut},
                helpers::Bytes
            }
        },
        ::core::{
            cmp::{Ord, Ordering},
            convert::From,
            fmt::{Debug, Display},
            marker::Sized,
            ptr::{self, NonNull},
            result::Result::{self, Err, Ok}
        }
    };

    #[cfg_attr(miri, track_caller)]
    pub unsafe fn grow_mut<A: GrowMut<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
        a: &mut A,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        b: Bytes
    ) -> Result<NonNull<u8>, E> {
        match old_layout.size().cmp(&new_layout.size()) {
            Ordering::Less => grow_unchecked_mut(a, ptr, old_layout, new_layout, b),
            Ordering::Equal => {
                let old_align = old_layout.align();
                let new_align = new_layout.align();
                match new_align.cmp(&old_align) {
                    Ordering::Greater => grow_unchecked_mut(a, ptr, old_layout, new_layout, b),
                    Ordering::Equal => Ok(ptr),
                    Ordering::Less => Err(E::from(Error::ReallocSmallerAlign(old_align, new_align)))
                }
            }
            Ordering::Greater => {
                Err(E::from(Error::GrowSmallerNewLayout(old_layout.size(), new_layout.size())))
            }
        }
    }

    #[cfg_attr(miri, track_caller)]
    pub unsafe fn grow_unchecked_mut<
        A: GrowMut<Error = E> + ?Sized,
        E: From<Error> + Debug + Display
    >(
        a: &mut A,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        b: Bytes
    ) -> Result<NonNull<u8>, E> {
        let old_size = old_layout.size();
        let new_ptr = match b {
            Bytes::Uninitialized => tri!(do a.alloc_mut(new_layout)),
            Bytes::Zeroed => tri!(do a.zalloc_mut(new_layout))
        };

        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
        if old_size != 0 {
            tri!(do a.try_dealloc_mut(ptr, old_layout));
        }

        Ok(new_ptr)
    }

    #[cfg_attr(miri, track_caller)]
    pub unsafe fn shrink_unchecked_mut<
        A: ShrinkMut<Error = E> + ?Sized,
        E: From<Error> + Debug + Display
    >(
        a: &mut A,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, E> {
        let new_ptr = tri!(do a.alloc_mut(new_layout));

        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
        if old_layout.is_nonzero_sized() {
            tri!(do a.try_dealloc_mut(ptr, old_layout));
        }

        Ok(new_ptr)
    }

    #[cfg_attr(miri, track_caller)]
    pub unsafe fn ralloc_mut<
        A: ReallocMut<Error = E> + ?Sized,
        E: From<Error> + Debug + Display
    >(
        a: &mut A,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        b: Bytes
    ) -> Result<NonNull<u8>, E> {
        match old_layout.size().cmp(&new_layout.size()) {
            Ordering::Less => grow_unchecked_mut(a, ptr, old_layout, new_layout, b),
            Ordering::Equal => {
                let old_align = old_layout.align();
                let new_align = new_layout.align();
                match new_align.cmp(&old_align) {
                    Ordering::Greater => shrink_unchecked_mut(a, ptr, old_layout, new_layout),
                    Ordering::Equal => Ok(ptr),
                    Ordering::Less => Err(E::from(Error::ReallocSmallerAlign(old_align, new_align)))
                }
            }
            Ordering::Greater => shrink_unchecked_mut(a, ptr, old_layout, new_layout)
        }
    }
}
