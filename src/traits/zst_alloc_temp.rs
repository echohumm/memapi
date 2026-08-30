use {
    crate::{
        error::Error,
        layout::Layout,
        traits::{
            AllocDescriptor,
            zst_alloc::{ZstAlloc, ZstBasicAlloc, ZstDealloc}
        }
    },
    ::core::{
        convert::From,
        fmt::{Debug, Display},
        ops::FnOnce,
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    }
};

#[allow(unused_imports)] use crate::error::Cause;

/// A memory allocation interface which may only be able to provide temporary, scoped allocations
/// and carries no internal state.
///
/// Because implementors hold no state relevant to allocation, its operations are exposed as
/// associated functions taking no `self` receiver.
pub trait ZstAllocTemp: AllocDescriptor {
    /// Attempts to allocate a block of memory fitting the given [`Layout`], and calls `with_mem` on
    /// the returned pointer on success.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   `::std::io::Error::last_os_error().raw_os_error()`.
    /// - <code>Err([Error::Other]\(msg\))</code> for allocator-specific failures.
    ///
    /// # Safety
    ///
    /// Safety preconditions are implementation defined.
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        layout: Layout,
        with_mem: F
    ) -> Result<R, Self::Error>;

    /// Attempts to allocate a block of zeroed memory fitting the given [`Layout`], and calls
    /// `with_mem` on the returned pointer on success.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if allocation fails. `cause` is
    ///   typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
    ///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
    ///   `::std::io::Error::last_os_error().raw_os_error()`.
    /// - <code>Err([Error::Other]\(msg\))</code> for allocator-specific failures.
    ///
    /// # Safety
    ///
    /// Safety preconditions are implementation defined.
    #[cfg_attr(miri, track_caller)]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        layout: Layout,
        with_mem: F
    ) -> Result<R, Self::Error> {
        Self::alloc_temp(layout, |ptr: NonNull<u8>| {
            ::core::ptr::write_bytes(ptr.as_ptr(), 0, layout.size());
            with_mem(ptr)
        })
    }
}

impl<A: ZstBasicAlloc> ZstAllocTemp for A {
    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn alloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        layout: Layout,
        with_mem: F
    ) -> Result<R, A::Error> {
        alloc_temp_with(layout, with_mem, <A as ZstAlloc>::alloc, <A as ZstDealloc>::try_dealloc)
    }

    #[cfg_attr(miri, track_caller)]
    #[inline]
    unsafe fn zalloc_temp<R, F: FnOnce(NonNull<u8>) -> R>(
        layout: Layout,
        with_mem: F
    ) -> Result<R, A::Error> {
        alloc_temp_with(layout, with_mem, <A as ZstAlloc>::zalloc, <A as ZstDealloc>::try_dealloc)
    }
}

unsafe fn alloc_temp_with<R, E: From<Error> + Debug + Display, F: FnOnce(NonNull<u8>) -> R>(
    layout: Layout,
    f: F,
    alloc: fn(Layout) -> Result<NonNull<u8>, E>,
    dealloc: unsafe fn(NonNull<u8>, Layout) -> Result<(), E>
) -> Result<R, E> {
    match alloc(layout) {
        Ok(ptr) => {
            let ret = f(ptr);
            tri!(do dealloc(ptr, layout));
            Ok(ret)
        }
        Err(e) => Err(e)
    }
}
