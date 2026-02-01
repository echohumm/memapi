use {
    crate::{Layout, error::Error},
    core::{
        ffi::c_void,
        mem::{ManuallyDrop, MaybeUninit},
        ptr::NonNull
    }
};

#[cfg(feature = "catch_unwind")]
thread_local! {
    static UNWIND: core::cell::RefCell<bool> =
        core::cell::RefCell::new(false);
}

/// Attempts to allocate a block of memory fitting the given [`Layout`] on the stack with C
/// `alloca`. On success, calls `f` with the allocation and a pointer to the output value which is
/// returned.
///
/// The allocation is only valid for the duration of the call. If `zero` is true, the allocation
/// is zeroed.
///
/// If [`layout.size()`](Layout::size) is zero, `f` will receive a [`dangling`](core::ptr::dangling)
/// pointer.
///
/// # Errors
///
/// <code>Err([Error::CaughtUnwind])</code> when `f` panics if `catch_unwind` is enabled.
///
/// # Safety
///
/// The caller must ensure:
/// - `layout` is valid and <code>[layout.size()](Layout::size) + ([layout.align()](Layout::align) -
///   1)</code> will not exceed the stack allocation limit.
/// - If `layout.size() == 0`, `f` must treat the pointer as a dangling, properly aligned pointer.
/// - `f` must initialize `out` before returning.
/// - On Rust versions below `1.71` with `catch_unwind` disabled, `f` must never unwind.
pub unsafe fn with_alloca<R, F: FnOnce(NonNull<u8>, *mut R)>(
    layout: Layout,
    zero: bool,
    f: F
) -> Result<R, Error> {
    let mut ret = MaybeUninit::uninit();
    let mut data = ManuallyDrop::new(f);

    // SAFETY: TODO
    unsafe {
        c_alloca(
            layout.size(),
            layout.align(),
            zero,
            c_call_callback::<R, F>,
            (&mut data as *mut ManuallyDrop<F>).cast::<c_void>(),
            (&mut ret as *mut MaybeUninit<R>).cast::<c_void>()
        );
    }
    #[cfg(feature = "catch_unwind")]
    if UNWIND.with(|v| v.replace(false)) {
        return Err(Error::CaughtUnwind);
    }
    // SAFETY: the closure will have initialized ret with the return value of the callback provided
    // by the user.
    Ok(unsafe { ret.assume_init() })
}

// TODO: dedup below

#[rustversion::before(1.71)]
/// Helper to call `callback` with `NonNull::new_unchecked(ptr)` and `out` as arguments to
/// `callback` from C.
pub unsafe extern "C" fn c_call_callback<R, F: FnOnce(NonNull<u8>, *mut R)>(
    callback: *mut c_void,
    ptr: *mut u8,
    out: *mut c_void
) {
    #[cfg(not(feature = "catch_unwind"))]
    {
        ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>())(
            NonNull::new_unchecked(ptr),
            out.cast()
        );
    }
    #[cfg(feature = "catch_unwind")]
    {
        let f = ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            f(NonNull::new_unchecked(ptr), out.cast());
        }));
        if result.is_err() {
            UNWIND.with(|v| *v.borrow_mut() = true);
        }
    }
}
#[rustversion::since(1.71)]
/// Helper to call `callback` with `NonNull::new_unchecked(ptr)` and `out` as arguments to
/// `callback` from C.
pub unsafe extern "C-unwind" fn c_call_callback<R, F: FnOnce(NonNull<u8>, *mut R)>(
    callback: *mut c_void,
    ptr: *mut u8,
    out: *mut c_void
) {
    #[cfg(not(feature = "catch_unwind"))]
    {
        ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>())(
            NonNull::new_unchecked(ptr),
            out.cast()
        );
    }
    #[cfg(feature = "catch_unwind")]
    {
        let f = ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            f(NonNull::new_unchecked(ptr), out.cast());
        }));
        if result.is_err() {
            UNWIND.with(|v| *v.borrow_mut() = true);
        }
    }
}

#[rustversion::before(1.71)]
extern "C" {
    /// Allocates `size` bytes on the stack with at least `align` alignment and call `cb(closure,
    /// allocation, out)`.
    ///
    /// The allocation is only valid for the duration of this call. If `zero` is true, the
    /// allocation is zeroed.
    ///
    /// If `size == 0`, `cb` receives a dangling, aligned pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `align` is a nonzero power of two.
    /// - `size + (align - 1)` will not overflow or exceed the stack allocation limit.
    /// - `cb` does not store the pointer or use it after the call returns.
    /// - `cb` initializes `out` if the caller expects a value to be written there.
    pub fn c_alloca(
        size: usize,
        align: usize,
        zero: bool,
        cb: unsafe extern "C" fn(*mut c_void, *mut u8, *mut c_void),
        closure: *mut c_void,
        out: *mut c_void
    );
}
#[rustversion::since(1.71)]
extern "C-unwind" {
    /// Allocates `size` bytes on the stack with at least `align` alignment and call `cb(closure,
    /// allocation, out)`.
    ///
    /// The allocation is only valid for the duration of this call. If `zero` is true, the
    /// allocation is zeroed.
    ///
    /// If `size == 0`, `cb` receives a dangling, aligned pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `align` is a nonzero power of two.
    /// - `size + (align - 1)` will not overflow or exceed the stack allocation limit.
    /// - `cb` does not store the pointer or use it after the call returns.
    /// - `cb` initializes `out` if the caller expects a value to be written there.
    pub fn c_alloca(
        size: usize,
        align: usize,
        zero: bool,
        cb: unsafe extern "C-unwind" fn(*mut c_void, *mut u8, *mut c_void),
        closure: *mut c_void,
        out: *mut c_void
    );
}
