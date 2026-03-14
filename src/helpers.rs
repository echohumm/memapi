use {
    crate::{
        error::{Cause, Error},
        layout::Layout,
        traits::data::type_props::{
            varsized_nonnull_from_parts,
            varsized_ptr_from_parts,
            varsized_ptr_from_parts_mut
        }
    },
    ::core::{
        ptr::NonNull,
        result::Result::{self, Err, Ok}
    }
};

#[allow(unused_imports)] use crate::traits::data::type_props::SizedProps;

/// The maximum value of a `usize` with no high bit.
///
/// Equivalent to <code>[usize::MAX] >> 1</code> or <code>[isize::MAX] as usize</code>.
pub const USIZE_MAX_NO_HIGH_BIT: usize = usize::MAX >> 1;

/// A `usize` in which only the high bit is set.
///
/// Equivalent to <code>[usize::MAX] ^ ([usize::MAX] >> 1)</code>, <code>[usize::MAX] <<
/// ([usize::BITS] - 1)</code>, or <code>[USIZE_MAX_NO_HIGH_BIT] + 1</code>.
pub const USIZE_HIGH_BIT: usize = usize::MAX ^ (USIZE_MAX_NO_HIGH_BIT);

/// A pointer to a [`c_void`](::core::ffi::c_void).
#[allow(non_camel_case_types)]
pub type void_ptr = *mut ::core::ffi::c_void;

#[cfg(target_pointer_width = "64")]
/// Unsigned integer type that is twice the bit-width of `usize`.
///
/// On 64-bit targets this is an alias for `u128`.
#[allow(non_camel_case_types)]
pub type udouble = u128;

#[cfg(target_pointer_width = "32")]
/// Unsigned integer type that is twice the bit-width of `usize`.
///
/// On 32-bit targets this is an alias for `u64`.
#[allow(non_camel_case_types)]
pub type udouble = u64;

#[cfg(target_pointer_width = "16")]
/// Unsigned integer type that is twice the bit-width of `usize`.
///
/// On 16-bit targets this is an alias for `u32`.
#[allow(non_camel_case_types)]
pub type udouble = u32;

/// Aligns the given value `v` up to the next multiple of `align`.
///
/// # Safety
///
/// This function is safe to call, but the returned value may be incorrect if `align` is not a power
/// of two. An overflow or underflow may also occur if:
/// - `align == 0`
/// - `v + (align - 1)` exceeds [`usize::MAX`]
#[cfg_attr(any(miri, debug_assertions), track_caller)]
#[must_use]
#[inline]
pub const unsafe fn align_up(v: usize, align: usize) -> usize {
    assert_unsafe_precondition!(
        "`align_up` requires that `align` is a non-zero power of two and that `v + (align - 1)` \
        does not overflow.",
        (align: usize = align, v: usize = v)
            => [align.is_power_of_two() && v <= usize::MAX - (align - 1)]
    );
    let m1 = align - 1;
    (v + m1) & !m1
}

/// Returns the maximum alignment satisfied by a non-null pointer.
#[cfg_attr(miri, track_caller)]
#[must_use]
#[inline]
pub fn ptr_max_align(ptr: NonNull<u8>) -> usize {
    let p = ptr.as_ptr() as usize;
    p & p.wrapping_neg()
}

/// Returns `true` if `ptr` is aligned to `align`.
///
/// # Safety
///
/// This function is safe to call, but the returned value may be incorrect if `align` is not a power
/// of two. An underflow may also occur if `align == 0`.
#[must_use]
pub unsafe fn is_aligned(ptr: *const u8, align: usize) -> bool {
    ptr as usize & (align - 1) == 0
}

/// Creates a <code>[NonNull]<\[T\]></code> from a pointer and a length.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
///
/// This is a helper used in place of [`NonNull::slice_from_raw_parts`], which was stabilized after
/// this crate's MSRV.
#[::rustversion::attr(since(1.61), const)]
#[must_use]
pub fn nonnull_slice_from_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
    varsized_nonnull_from_parts(p.cast(), len)
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
///
/// This is a helper used in place of
/// [`ptr::slice_from_raw_parts_mut`](::core::ptr::slice_from_raw_parts_mut), which was
/// const-stabilized after this crate's MSRV.
#[::rustversion::attr(since(1.61), const)]
#[must_use]
pub fn slice_ptr_from_parts_mut<T>(p: *mut T, len: usize) -> *mut [T] {
    varsized_ptr_from_parts_mut(p.cast(), len)
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// Note that this is only `const` on Rust versions 1.47 and above.
#[::rustversion::attr(since(1.61), const)]
#[must_use]
pub fn slice_ptr_from_parts<T>(p: *const T, len: usize) -> *const [T] {
    varsized_ptr_from_parts(p.cast(), len)
}

/// Returns the length of a [`NonNull`] slice pointer.
///
/// Note that this is only `const` on Rust versions 1.58 and above.
///
/// # Safety
///
/// The caller must ensure `ptr` is aligned and non-dangling.
#[::rustversion::attr(since(1.58), const)]
#[must_use]
#[inline]
pub unsafe fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    (&*(ptr.as_ptr() as *const [T])).len()
}

// for some reason, making these non-generic to take a *mut u8 instead causes up to a +590% perf
// loss soooo.. not doing that, i guess.
/// Converts a possibly null pointer into a [`NonNull`] result.
///
/// # Errors
///
/// <code>Err([Error::AllocFailed]\(layout, [Cause::Unknown]\)</code> if `ptr.is_null()`.
pub fn null_q<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, Error> {
    if ptr.is_null() {
        Err(Error::AllocFailed(layout, Cause::Unknown))
    } else {
        // SAFETY: we just checked that the pointer is non-null
        Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
    }
}

#[cfg(feature = "os_err_reporting")]
/// Converts a possibly null pointer into a [`NonNull`] result, including OS error info if
/// available.
///
/// OS error info is currently available as the `os_err_reporting` feature is enabled.
///
/// # Errors
///
/// <code>Err([Error::AllocFailed]\(layout, [Cause::OSErr]\(oserr\)\)</code>, where `oserr` is the
/// error from [`io::Error::last_os_error`](::std::io::Error::last_os_error), if `ptr.is_null()`.
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, Error> {
    if ptr.is_null() {
        Err(Error::AllocFailed(
            layout,
            // SAFETY: last_os_error is guaranteed to return a real os error
            // unfortunately we have to convert oserr -> i32 -> oserr because io::Error is not
            // Copy, and other traits which Cause is.
            Cause::OSErr(unsafe {
                ::std::io::Error::last_os_error()
                    .raw_os_error()
                    .unwrap_or_else(|| ::core::hint::unreachable_unchecked())
            })
        ))
    } else {
        // SAFETY: we just checked that the pointer is non-null
        Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
    }
}

#[cfg(not(feature = "os_err_reporting"))]
/// Converts a possibly null pointer into a [`NonNull`] result, including OS error info if
/// available.
///
/// OS error info is currently unavailable as the `os_err_reporting` feature is disabled.
///
/// # Errors
///
/// <code>Err([Error::AllocFailed]\(layout, [Cause::Unknown]\)</code> if `ptr.is_null()`.
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, Error> {
    null_q(ptr, layout)
}

/// Checks if `layout` is zero-sized, returns `Ok(layout.dangling())` if it is, otherwise returns
/// `null_q_dyn(alloc(layout), layout)`.
///
/// # Errors
///
/// See [`null_q_dyn`]
pub fn null_q_dyn_zsl_check<T, F: ::core::ops::FnOnce(Layout) -> *mut T>(
    alloc: F,
    layout: Layout
) -> Result<NonNull<u8>, Error> {
    if layout.size() == 0 { Ok(layout.dangling()) } else { null_q_dyn(alloc(layout), layout) }
}

#[::rustversion::since(1.49)]
/// Transmutes via a `union`. Performs no validity checks.
///
/// Note that this requires both <code>Src: [Copy]</code> and <code>Dst: [Copy]</code> on Rust
/// versions below 1.49, and is only `const` on 1.56 and above.
///
/// # Safety
///
/// The caller must ensure that <code>[Src::SZ](SizedProps::SZ) >=
/// [Dst::SZ](SizedProps::SZ)</code> and that `src` is a valid
/// `Dst`.
#[::rustversion::attr(since(1.56), const)]
pub unsafe fn union_transmute<Src, Dst>(src: Src) -> Dst {
    use ::core::mem::ManuallyDrop;
    union Either<Src, Dst> {
        src: ManuallyDrop<Src>,
        dst: ManuallyDrop<Dst>
    }

    assert_unsafe_precondition!(
        "`union_transmute` requires that `Src::SZ >= Dst::SZ`",
        <Src, Dst>() => [Src::SZ >= Dst::SZ]
    );

    ManuallyDrop::into_inner(Either { src: ManuallyDrop::new(src) }.dst)
}
#[::rustversion::before(1.49)]
/// Transmutes via a `union`. Performs no validity checks.
///
/// Note that this requires both <code>Src: [Copy]</code> and <code>Dst: [Copy]</code> on Rust
/// versions below 1.49, and is only `const` on 1.56 and above.
///
/// # Safety
///
/// The caller must ensure that <code>[Src::SZ] >= [Dst::SZ]</code> and that `src` is a valid `Dst`.
pub unsafe fn union_transmute<Src: ::core::marker::Copy, Dst: ::core::marker::Copy>(
    src: Src
) -> Dst {
    union Either<Src: ::core::marker::Copy, Dst: ::core::marker::Copy> {
        src: Src,
        dst: Dst
    }

    assert_unsafe_precondition!(
        noconst,
        "`union_transmute` requires that `Src::SZ >= Dst::SZ`",
        <Src, Dst>()
            => [Src::SZ >= Dst::SZ]
    );

    Either { src }.dst
}

/// Returns `true` if `lhs` is an integer multiple of `rhs`, and false otherwise.
///
/// This function is equivalent to `lhs % rhs == 0`, except that it will not panic
/// for `rhs == 0`. Instead, `0.is_multiple_of(0) == true`, and for any non-zero `n`,
/// `n.is_multiple_of(0) == false`.
#[must_use]
pub const fn is_multiple_of(lhs: usize, rhs: usize) -> bool {
    match rhs {
        0 => lhs == 0,
        _ => lhs % rhs == 0
    }
}

// AllocGuard/SliceAllocGuard removed as they are a bit out-of-scope. will likely be brought back in
// a separate crate later.
