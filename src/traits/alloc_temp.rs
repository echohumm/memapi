use {
    crate::{BasicAlloc, Layout, error::Error},
    core::{ptr, ptr::NonNull}
};

/// A memory allocation interface which may only be able to provide temporary, scoped allocations.
pub trait AllocTemp {
    /// <placeholder>
    unsafe fn alloc_temp<R, F: FnOnce(Result<NonNull<u8>, Error>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> R;
    /// <placeholder>
    unsafe fn zalloc_temp<R, F: FnOnce(Result<NonNull<u8>, Error>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> R {
        let closure = |ptrres: Result<NonNull<u8>, Error>| {
            if let Ok(ptr) = ptrres {
                ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
            }
            with_mem(ptrres)
        };

        self.alloc_temp(layout, closure)
    }
}

impl<A: BasicAlloc> AllocTemp for A {
    unsafe fn alloc_temp<R, F: FnOnce(Result<NonNull<u8>, Error>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> R {
        let ptr = self.alloc(layout);
        let ret = with_mem(ptr);
        if let Ok(ptr) = ptr {
            self.dealloc(ptr, layout);
        }
        ret
    }

    unsafe fn zalloc_temp<R, F: FnOnce(Result<NonNull<u8>, Error>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> R {
        let ptr = self.zalloc(layout);
        let ret = with_mem(ptr);
        if let Ok(ptr) = ptr {
            self.dealloc(ptr, layout);
        }
        ret
    }
}
