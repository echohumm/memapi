use {
    crate::{Layout, error::Error},
    core::{
        ffi::c_void,
        mem::{ManuallyDrop, MaybeUninit},
        ptr::NonNull
    }
};

/// <placeholder>
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
    // SAFETY: the closure will have initialized ret with the return value of the callback
    // provided by the user.
    Ok(unsafe { ret.assume_init() })
}

#[rustversion::before(1.71)]
/// Helper to call `callback` with `NonNull::new_unchecked(ptr)` and `out` as arguments to
/// `callback` from C.
pub unsafe extern "C" fn c_call_callback<R, F: FnOnce(NonNull<u8>, *mut R)>(
    callback: *mut c_void,
    ptr: *mut u8,
    out: *mut c_void
) {
    ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>())(
        NonNull::new_unchecked(ptr),
        out.cast()
    );
}
#[rustversion::since(1.71)]
/// Helper to call `callback` with `NonNull::new_unchecked(ptr)` and `out` as arguments to
/// `callback` from C.
pub unsafe extern "C-unwind" fn c_call_callback<R, F: FnOnce(NonNull<u8>, *mut R)>(
    callback: *mut c_void,
    ptr: *mut u8,
    out: *mut c_void
) {
    // TODO: catch unwinds and return result somehow, this will avoid c-unwind entirely and allow
    //  for better error reporting
    ManuallyDrop::take(&mut *callback.cast::<ManuallyDrop<F>>())(
        NonNull::new_unchecked(ptr),
        out.cast()
    );
}

#[rustversion::before(1.71)]
extern "C" {
    /// <placeholder>
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
    /// <placeholder>
    pub fn c_alloca(
        size: usize,
        align: usize,
        zero: bool,
        cb: unsafe extern "C-unwind" fn(*mut c_void, *mut u8, *mut c_void),
        closure: *mut c_void,
        out: *mut c_void
    );
}
