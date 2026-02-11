use {
    crate::{BasicAlloc, Layout, error::Error},
    ::core::{
        convert::From,
        fmt::{Debug, Display},
        ops::FnOnce,
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok}
    }
};

#[allow(unused_imports)] use crate::error::Cause;

/// A memory allocation interface which may only be able to provide temporary, scoped allocations.
pub trait AllocTemp {
    /// The error type returned by this allocator.
    type Error: From<Error> + Debug + Display;

    /// Attempts to allocate a block of memory fitting the given [`Layout`], and calls `with_mem` on
    /// the returned pointer on success.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocTemp::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>[layout.size()](Layout::size) ==
    ///   0</code>.
    /// - <code>Err([Error::CaughtUnwind])</code> if the `catch_unwind` feature is enabled and an
    ///   unwind occurs in a function which is not allowed to unwind.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    ///
    /// # Safety
    ///
    /// Safety preconditions are implementation defined.
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Self::Error>;

    /// Attempts to allocate a block of zeroed memory fitting the given [`Layout`], and calls
    /// `with_mem` on the returned pointer on success.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocTemp::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
    /// - <code>Err([Error::ZeroSizedLayout])</code> if <code>[layout.size()](Layout::size) ==
    ///   0</code>.
    /// - <code>Err([Error::CaughtUnwind])</code> if the `catch_unwind` feature is enabled and an
    ///   unwind occurs in a function which is not allowed to unwind.
    ///
    /// [last_os_error]: ::std::io::Error::last_os_error
    /// [raw_os_error]: ::std::io::Error::raw_os_error
    ///
    /// # Safety
    ///
    /// Safety preconditions are implementation defined.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, Self::Error> {
        self.alloc_temp(layout, |ptr: NonNull<u8>| {
            ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
            with_mem(ptr)
        })
    }
}

impl<A: BasicAlloc> AllocTemp for A {
    type Error = A::Error;

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, A::Error> {
        alloc_temp_with(self, layout, with_mem, A::alloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        &self,
        layout: Layout,
        with_mem: F
    ) -> Result<R, A::Error> {
        alloc_temp_with(self, layout, with_mem, A::zalloc)
    }
}

unsafe fn alloc_temp_with<
    A: BasicAlloc<Error = E>,
    R,
    E: From<Error> + Debug + Display,
    F: FnOnce(NonNull<u8>) -> R
>(
    a: &A,
    layout: Layout,
    f: F,
    alloc: fn(&A, Layout) -> Result<NonNull<u8>, E>
) -> Result<R, E> {
    match alloc(a, layout) {
        Ok(ptr) => {
            let ret = f(ptr);
            tri!(do a.try_dealloc(ptr, layout));
            Ok(ret)
        }
        Err(e) => Err(e)
    }
}
