use {
    crate::{layout::Layout, traits::AllocDescriptor},
    ::core::{
        ptr::NonNull,
        result::Result::{self}
    }
};

#[allow(unused_imports)] use crate::error::{Cause, Error};

// TODO: make sure docs are correct. current are ai-generated so...

// TODO: could auto impl *+*Mut, etc. for A: Zst*? would simplify allocator impls for zst
//  allocators, but could slow down compilation (unlikely but potential runtime overhead too)

/// A memory allocation interface which carries no internal state.
///
/// Because implementors hold no state relevant to allocation, its operations are exposed as
/// associated functions taking no `self` receiver.
pub trait ZstAlloc: AllocDescriptor {
    /// Attempts to allocate a block of memory fitting the given [`Layout`].
    ///
    /// If <code>layout.[size](Layout::size)() == 0</code>, no allocation will be performed and a
    /// [dangling](::core::ptr::dangling) pointer will be returned.
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
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures.
    fn alloc(layout: Layout) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

    /// Attempts to allocate a zeroed block of memory fitting the given [`Layout`].
    ///
    /// If <code>layout.[size](Layout::size)() == 0</code>, no allocation will be performed and a
    /// [dangling](::core::ptr::dangling) pointer will be returned.
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
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures.
    fn zalloc(layout: Layout) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;
}

/// A stateless memory allocation interface which can also deallocate memory.
pub trait ZstDealloc: ZstAlloc {
    /// Deallocates a previously allocated block.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](::core::ptr::dangling).
    ///
    /// Unlike [`Dealloc::dealloc`](crate::traits::alloc::Dealloc::dealloc), this reports failure
    /// through its returned [`Result`] rather than panicking, as there is no `self` on which a
    /// panicking convenience wrapper could be provided.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// This method will not return an error if `ptr` is [dangling](::core::ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    unsafe fn dealloc(
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocDescriptor>::Error>;

    /// Attempts to deallocate a previously allocated block. If this allocator is backed by an
    /// allocation library which does not provide fallible deallocation operations, this may panic,
    /// abort, or incorrectly return `Ok(())`.
    ///
    /// This is a noop if <code>layout.[size](Layout::size)() == 0</code> or `ptr` is
    /// [dangling](::core::ptr::dangling).
    ///
    /// Note that this function differs from checked deallocation in that it may still cause
    /// undefined behavior if it receives invalid inputs.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block of memory allocated using this allocator.
    /// - `layout` describes exactly the same block.
    ///
    /// # Errors
    ///
    /// Errors are implementation-defined, refer to [`AllocDescriptor::Error`] and [`Error`].
    ///
    /// The standard implementations may return:
    /// <code>Err([Error::Unsupported])</code> if deallocation is unsupported. In this case,
    /// reallocation via [`ZstRealloc`] may still be supported.
    ///
    /// This method will not return an error if `ptr` is [dangling](::core::ptr::dangling) or if
    /// <code>layout.[size](Layout::size)() == 0</code>. Instead, no action will be performed.
    unsafe fn try_dealloc(
        ptr: NonNull<u8>,
        layout: Layout
    ) -> Result<(), <Self as AllocDescriptor>::Error>;
}

// TODO: default impls
/// A stateless memory allocation interface which can arbitrarily resize allocations.
pub trait ZstRealloc: ZstDealloc {
    /// Reallocates a block, growing or shrinking as needed. The new alignment may be larger or the
    /// same, but cannot be smaller.
    ///
    /// On grow, preserves existing contents up to <code>old_layout.[size](Layout::size)()</code>,
    /// and on shrink, truncates to <code>new_layout.[size](Layout::size)()</code>.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// If `ptr` is dangling and `old_layout` is zero-sized, this will behave the same as
    /// [`ZstAlloc::alloc`].
    ///
    /// If `new_layout` is zero-sized, assuming that is a valid call (meaning `old_layout` is as
    /// well, and `ptr` is dangling), a new dangling pointer will be returned. This new pointer may
    /// have a different address if <code>new_layout.[align](Layout::align)() >
    /// old_layout.[align](Layout::align)()</code>.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block previously allocated with this allocator.
    /// - `old_layout` describes exactly the same block.
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
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures.
    unsafe fn realloc(
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;

    /// Reallocates a block, growing or shrinking as needed, with extra bytes being zeroed. The new
    /// alignment may be larger or the same, but cannot be smaller.
    ///
    /// On grow, preserves existing contents up to <code>old_layout.[size](Layout::size)()</code>,
    /// and on shrink, truncates to <code>new_layout.[size](Layout::size)()</code>.
    ///
    /// On failure, the original memory will not be deallocated.
    ///
    /// If `ptr` is dangling and `old_layout` is zero-sized, this will behave the same as
    /// [`ZstAlloc::alloc`].
    ///
    /// If `new_layout` is zero-sized, assuming that is a valid call (meaning `old_layout` is as
    /// well, and `ptr` is dangling), a new dangling pointer will be returned. This new pointer may
    /// have a different address if <code>new_layout.[align](Layout::align)() >
    /// old_layout.[align](Layout::align)()</code>.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `ptr` points to a block previously allocated with this allocator.
    /// - `old_layout` describes exactly the same block.
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
    /// - <code>Err([Error::ReallocSmallerAlign]\(old, new\))</code> if
    ///   <code>old_layout.[align](Layout::align)() > new_layout.[align](Layout::align)()</code>.
    /// - <code>Err([Error::Other]\(err\))</code> for allocator-specific failures.
    unsafe fn rezalloc(
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<u8>, <Self as AllocDescriptor>::Error>;
}
