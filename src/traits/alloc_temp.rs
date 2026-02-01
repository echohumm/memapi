use {
    crate::{BasicAlloc, Layout, error::Error},
    core::{ptr, ptr::NonNull}
};

/// A memory allocation interface which may only be able to provide temporary, scoped allocations.
pub trait AllocTemp {
    /// Attempts to allocate a block of memory fitting the given [`Layout`], and calls `with_mem` on
    /// the returned pointer on success.
    ///
    /// The pointer will be dangling if <code>[layout.size()](Layout::size) == 0</code>.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    ///
    /// # Safety
    ///
    /// Safety preconditions are implementation defined.
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error>;

    /// Attempts to allocate a block of zeroed memory fitting the given [`Layout`], and calls
    /// `with_mem` on the returned pointer on success.
    ///
    /// The pointer will be dangling if <code>[layout.size()](Layout::size) == 0</code>.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`Error`].
    ///
    /// The standard implementations may return:
    /// - [`Err(Error::AllocFailed(layout, cause))`](Error::AllocFailed) if allocation fails.
    ///   `cause` is typically [`Cause::Unknown`](crate::error::Cause::Unknown). If an OS error is
    ///   available, it may be [`Cause::OSErr(oserr)`](crate::error::Cause::OSErr). In this case,
    ///   `oserr` will be the error from
    ///   <code>[std::io::Error::last_os_error].[raw_os_error()](std::io::Error::raw_os_error)</
    ///   code>.
    ///
    /// # Safety
    ///
    /// Safety preconditions are implementation defined.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        self.alloc_temp(layout, |ptr: NonNull<u8>| {
            ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
            with_mem(ptr)
        })
    }
}

impl<A: BasicAlloc> AllocTemp for A {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        alloc_temp_with(self, layout, with_mem, A::alloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Error> {
        alloc_temp_with(self, layout, with_mem, A::zalloc)
    }
}

unsafe fn alloc_temp_with<A: BasicAlloc, R, F: FnOnce(NonNull<u8>) -> R>(
    a: &A,
    layout: Layout,
    f: F,
    alloc: fn(&A, Layout) -> Result<NonNull<u8>, Error>
) -> Result<R, Error> {
    match alloc(a, layout) {
        Ok(ptr) => {
            let ret = f(ptr);
            tri!(err a.try_dealloc(ptr, layout));
            Ok(ret)
        }
        Err(e) => Err(e)
    }
}
