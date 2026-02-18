use {
    crate::{error::Error, layout::Layout},
    ::core::{
        ffi::c_void,
        mem::{ManuallyDrop, MaybeUninit},
        ops::FnOnce,
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    }
};

#[cfg(feature = "catch_unwind")]
::std::thread_local! {
    static UNWIND: ::core::cell::RefCell<bool> =
        ::core::cell::RefCell::new(false);
}

/// Attempts to allocate a block of memory fitting the given [`Layout`] on the stack with C
/// `alloca`. On success, calls `f` with the allocation and a pointer to the output value which is
/// returned.
///
/// The allocation is only valid for the duration of the call.
///
/// If <code>layout.[size](Layout::size)()</code> is zero, `f` will receive a
/// [`dangling`](::core::ptr::dangling) pointer.
///
/// # Errors
///
/// <code>Err([Error::CaughtUnwind])</code> when `f` panics if `catch_unwind` is enabled.
///
/// # Safety
///
/// The caller must ensure:
/// - `layout` is valid and <code>layout.[size](Layout::size)() + (layout.[align](Layout::align)() -
///   1)</code> will not exceed the stack allocation limit.
/// - If `layout.size() == 0`, `f` must treat the pointer as a [`dangling`](::core::ptr::dangling)
///   pointer.
/// - `f` must initialize the value behind its second parameter before returning.
/// - On Rust versions below `1.71` with `catch_unwind` disabled, `f` must never unwind.
pub unsafe fn with_alloca<R, F: FnOnce(NonNull<u8>, *mut R)>(
    layout: Layout,
    f: F
) -> Result<R, Error> {
    if layout.size() == 0 {
        return Err(Error::ZeroSizedLayout);
    }

    let mut ret = MaybeUninit::uninit();
    let mut closure = ManuallyDrop::new(f);

    // SAFETY: we declare this function in C as:
    // ```
    // void c_alloca(
    //     const size_t size,
    //     const size_t align,
    //     void (*callback)(void*, uint8_t*, void*),
    //     void* closure,
    //     void* out
    // )
    // ```
    // in rust we declare it as
    // ```
    // pub fn c_alloca(
    //     size: usize,
    //     align: usize,
    //     cb: unsafe extern $ffi fn(*mut c_void, *mut u8, *mut c_void),
    //     closure: *mut c_void,
    //     out: *mut c_void
    // )
    // ```
    // so:
    // - the return types match as `()` == `void`
    // - the size and align parameters match as `usize` == `size_t`
    // - the callback types match as the rust callback is defined as `extern "C"`
    // - the `closure` pointer points to a valid closure which `cb` can call
    // - the `ret` pointer points to a valid `R` which `closure` initializes
    // additionally:
    // - the caller guarantees that `closure` cannot unwind in an unsafe environment
    // - the c function is safe
    unsafe {
        c_alloca(
            layout.size(),
            layout.align(),
            c_call_callback::<R, F>,
            (&mut closure as *mut ManuallyDrop<F>).cast::<c_void>(),
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

macro_rules! c_cb {
    ($verdef:ident, $ffi:literal) => {
        #[::rustversion::$verdef(1.71)]
        /// Helper to call `callback` with `NonNull::new_unchecked(ptr)` and `out` from C.
        ///
        /// # Safety
        ///
        /// - `callback` must be a valid pointer to an `F`.
        /// - `callback` must initialize the value behind its second parameter.
        /// - `ptr` must be a valid pointer which `callback` expects.
        /// - `out` must be a valid pointer to an `R`.
        pub unsafe extern $ffi fn c_call_callback<R, F: FnOnce(NonNull<u8>, *mut R)>(
            callback: *mut c_void,
            ptr: *mut u8,
            out: *mut c_void
        ) {
            let run = || {
                ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>())(
                    NonNull::new_unchecked(ptr),
                    out.cast()
                );
            };
            #[cfg(not(feature = "catch_unwind"))]
            run();
            #[cfg(feature = "catch_unwind")]
            if $ffi == "C-unwind" {
                if ::std::panic::catch_unwind(::std::panic::AssertUnwindSafe(run)).is_err() {
                    UNWIND.with(|v| *v.borrow_mut() = true);
                }
            } else {
                run();
            }
        }
    };
}
macro_rules! c_ext {
    ($verdef:ident, $ffi:literal) => {
        #[::rustversion::$verdef(1.71)]
        extern $ffi {
            /// Allocates `size` bytes on the stack with at least `align` alignment and calls
            /// `cb(closure, allocation, out)`.
            ///
            /// The allocation is only valid for the duration of this call.
            ///
            /// If `size == 0`, `cb` receives a [`dangling`](::core::ptr::dangling) pointer.
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
                cb: unsafe extern $ffi fn(*mut c_void, *mut u8, *mut c_void),
                closure: *mut c_void,
                out: *mut c_void
            );
        }
    };
}

c_cb! { before, "C" }
c_cb! { since, "C-unwind" }

c_ext! { before, "C" }
c_ext! { since, "C-unwind" }
