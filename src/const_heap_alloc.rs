use core::{
    alloc::Layout,
    error::Error,
    fmt::Display,
    intrinsics::{const_allocate, const_deallocate, const_eval_select},
    ptr::NonNull,
};

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// An allocator which allocates memory constantly in the heap.
///
/// # NOTE: This is primarily a stub for when constant trait methods are available.
pub struct ConstAlloc;

impl ConstAlloc {
    /// Allocates memory constantly.
    ///
    /// # Errors
    ///
    /// Returns `Err(`[`NonConstErr`]`)` if called at runtime.
    #[track_caller]
    #[inline]
    pub const fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, NonConstErr> {
        #[allow(unused_unsafe)]
        unsafe {
            const_eval_select((layout,), alloc_unchecked, alloc_fail)
        }
    }

    /// Allocates zeroed memory constantly.
    ///
    /// # Errors
    ///
    /// Returns `Err(`[`NonConstErr`]`)` if called at runtime.
    pub const fn alloc_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, NonConstErr> {
        match self.alloc(layout) {
            Ok(p) => {
                unsafe {
                    p.write_bytes(0, layout.size());
                }
                Ok(p)
            }
            Err(e) => Err(e),
        }
    }

    /// Deallocates constant memory.
    ///
    /// # Safety
    ///
    /// Does not deallocate if `ptr` was not allocated in the current constant.
    ///
    /// # Errors
    ///
    /// Returns `Err(`[`NonConstErr`]`)` if called at runtime.
    #[track_caller]
    #[inline]
    pub const unsafe fn dealloc(
        &self,
        ptr: NonNull<u8>,
        layout: Layout,
    ) -> Result<(), NonConstErr> {
        const_eval_select((ptr, layout), dealloc_unchecked, dealloc_fail)
    }
}

#[allow(clippy::unnecessary_wraps)]
const fn dealloc_unchecked(ptr: NonNull<u8>, layout: Layout) -> Result<(), NonConstErr> {
    unsafe {
        const_deallocate(ptr.as_ptr(), layout.size(), layout.align());
    }
    Ok(())
}

#[allow(clippy::unnecessary_wraps)]
const fn alloc_unchecked(layout: Layout) -> Result<NonNull<u8>, NonConstErr> {
    Ok(unsafe { NonNull::new_unchecked(const_allocate(layout.size(), layout.align())) })
}

const fn dealloc_fail(_: NonNull<u8>, _: Layout) -> Result<(), NonConstErr> {
    Err(NonConstErr)
}

const fn alloc_fail(_: Layout) -> Result<NonNull<u8>, NonConstErr> {
    Err(NonConstErr)
}

#[derive(Debug)]
/// Error for when a constant-only operation was attempted at runtime.
pub struct NonConstErr;

impl Display for NonConstErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "non-const call of constant-only method")
    }
}

impl Error for NonConstErr {}
