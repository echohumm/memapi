use {
    crate::{
        error::Error,
        layout::Layout,
        traits::alloc::{Grow, Realloc, Shrink}
    },
    ::core::{
        cmp::{Ord, Ordering},
        convert::From,
        fmt::{Debug, Display},
        marker::Sized,
        panic,
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok}
    }
};

pub fn default_dealloc_panic<E: Display>(ptr: NonNull<u8>, layout: Layout, e: E) -> ! {
    panic!("deallocation of block at {:p} with layout {:?} failed: {}", ptr.as_ptr(), layout, e)
}

// TODO: fast path that just deallocates and returns dangling if new size is 0?

//noinspection DuplicatedCode
#[cfg_attr(miri, track_caller)]
pub unsafe fn grow<A: Grow<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, E> {
    match new_layout.size().cmp(&old_layout.size()) {
        Ordering::Greater => grow_unchecked(a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            // TODO: maybe smaller align should be an error? in most cases that's ub
            if new_layout.align() > old_layout.align() {
                grow_unchecked(a, ptr, old_layout, new_layout, b)
            } else {
                Ok(ptr)
            }
        }
        Ordering::Less => {
            Err(E::from(Error::GrowSmallerNewLayout(old_layout.size(), new_layout.size())))
        }
    }
}

#[cfg_attr(miri, track_caller)]
pub unsafe fn grow_unchecked<A: Grow<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, E> {
    let old_size = old_layout.size();
    let new_ptr = match b {
        Bytes::Uninitialized => tri!(do a.alloc(new_layout)),
        Bytes::Zeroed => tri!(do a.zalloc(new_layout))
    };

    if old_size != 0 {
        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
        tri!(do a.try_dealloc(ptr, old_layout));
    }

    Ok(new_ptr)
}

#[cfg_attr(miri, track_caller)]
pub unsafe fn shrink_unchecked<A: Shrink<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout
) -> Result<NonNull<u8>, E> {
    let new_ptr = tri!(do a.alloc(new_layout));

    if old_layout.is_nonzero_sized() {
        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size());
        tri!(do a.try_dealloc(ptr, old_layout));
    }

    Ok(new_ptr)
}

//noinspection DuplicatedCode
#[cfg_attr(miri, track_caller)]
pub unsafe fn ralloc<A: Realloc<Error = E> + ?Sized, E: From<Error> + Debug + Display>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
    b: Bytes
) -> Result<NonNull<u8>, E> {
    match new_layout.size().cmp(&old_layout.size()) {
        Ordering::Greater => grow_unchecked(&a, ptr, old_layout, new_layout, b),
        Ordering::Equal => {
            if new_layout.align() > old_layout.align() {
                shrink_unchecked(&a, ptr, old_layout, new_layout)
            } else {
                Ok(ptr)
            }
        }
        Ordering::Less => shrink_unchecked(&a, ptr, old_layout, new_layout)
    }
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
                if new_layout.align() > old_layout.align() {
                    grow_unchecked_mut(a, ptr, old_layout, new_layout, b)
                } else {
                    Ok(ptr)
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
                if new_layout.align() > old_layout.align() {
                    grow_unchecked_mut(a, ptr, old_layout, new_layout, b)
                } else {
                    Ok(ptr)
                }
            }
            Ordering::Greater => shrink_unchecked_mut(a, ptr, old_layout, new_layout)
        }
    }
}
