use {
    crate::{
        error::{ArithErr, ArithOp, Cause, Error},
        layout::Layout,
        traits::data::type_props::{
            varsized_nonnull_from_parts,
            varsized_ptr_from_parts,
            varsized_ptr_from_parts_mut
        }
    },
    ::core::{
        marker::Sized,
        ops::Fn,
        option::Option::{self, None, Some},
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
/// [usize::BITS] - 1</code>, or <code>[USIZE_MAX_NO_HIGH_BIT] + 1</code>
pub const USIZE_HIGH_BIT: usize = usize::MAX ^ (USIZE_MAX_NO_HIGH_BIT);

/// Performs a checked arithmetic operation on two `usize`s.
///
/// Note that this is only `const` on Rust versions 1.47 and above.
///
/// # Errors
///
/// <code>Err([ArithErr]\(l, op, r\))</code> if the requested operation would cause an overflow,
/// underflow, or conversion error.
#[::rustversion::attr(since(1.47), const)]
pub fn checked_op(l: usize, op: ArithOp, r: usize) -> Result<usize, ArithErr> {
    #[::rustversion::since(1.52)]
    const fn checked_div(l: usize, r: usize) -> Option<usize> {
        l.checked_div(r)
    }
    #[::rustversion::before(1.52)]
    const fn checked_div(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l / r) }
    }

    #[::rustversion::since(1.73)]
    const fn checked_div_ceil(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l.div_ceil(r)) }
    }
    #[::rustversion::before(1.73)]
    const fn checked_div_ceil(l: usize, r: usize) -> Option<usize> {
        if r == 0 {
            None
        } else {
            let quo = l / r;
            let rem = l % r;
            if rem > 0 { Some(quo + 1) } else { Some(quo) }
        }
    }

    #[::rustversion::since(1.52)]
    const fn checked_rem(l: usize, r: usize) -> Option<usize> {
        l.checked_rem(r)
    }
    #[::rustversion::before(1.52)]
    const fn checked_rem(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l % r) }
    }

    #[::rustversion::since(1.50)]
    const fn checked_pow(l: usize, r: usize) -> Option<usize> {
        if r > u32::MAX as usize {
            None
        } else {
            #[allow(clippy::cast_possible_truncation)]
            l.checked_pow(r as u32)
        }
    }
    #[::rustversion::before(1.50)]
    #[::rustversion::attr(since(1.47), const)]
    fn checked_pow(l: usize, mut r: usize) -> Option<usize> {
        if r == 0 {
            return Some(1);
        }
        let mut base = l;
        let mut acc: usize = 1;

        loop {
            if (r & 1) == 1 {
                acc = tri!(opt acc.checked_mul(base));
                // since exp!=0, finally the exp must be 1.
                if r == 1 {
                    return Some(acc);
                }
            }
            r /= 2;
            base = tri!(opt base.checked_mul(base));
        }
    }

    let res = match op {
        // add, sub, and mul use an intrinsic and cannot be manually implemented afaik
        ArithOp::Add => l.checked_add(r),
        ArithOp::Sub => l.checked_sub(r),
        ArithOp::Mul => l.checked_mul(r),
        ArithOp::Div => checked_div(l, r),
        ArithOp::DivCeil => checked_div_ceil(l, r),
        ArithOp::Rem => checked_rem(l, r),
        ArithOp::Pow => checked_pow(l, r)
    };

    match res {
        Some(v) => Ok(v),
        None => Err(ArithErr(l, op, r))
    }
}

/// Aligns the given value `v` up to the next multiple of `align`.
///
/// # Safety
///
/// This function is safe to call, but the returned value may be incorrect if `align` is not a power
/// of two. An overflow or underflow may also occur if:
/// - `align == 0`
/// - `v + (align - 1)` exceeds [`usize::MAX`]
#[must_use]
#[inline]
pub const unsafe fn align_up(v: usize, align: usize) -> usize {
    assert_unsafe_precondition!("`align_up` requires that `align` is a non-zero power of two and that `v + (align - 1)` does not overflow.", (align: usize = align, v: usize = v) => align.is_power_of_two() && v <= usize::MAX - (align - 1));
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

/// Checks layout for being zero-sized, returning a [dangling](::core::ptr::dangling) pointer if it
/// is, otherwise attempting allocation using `f(layout)`.
///
/// # Errors
///
/// - <code>Err([Error::AllocFailed]\(layout, cause\))</code> if `f` returns a null pointer. `cause`
///   is typically [`Cause::Unknown`]. If the `os_err_reporting` feature is enabled, it will be
///   <code>[Cause::OSErr]\(oserr\)</code>. In this case, `oserr` will be the error from
///   <code>[last_os_error]\(\).[raw_os_error]\(\)</code>.
/// - <code>Err([Error::ZeroSizedLayout])</code> if <code>layout.[size](Layout::size)() == 0</code>.
///
/// [last_os_error]: ::std::io::Error::last_os_error
/// [raw_os_error]: ::std::io::Error::raw_os_error
#[inline]
pub fn null_q_dyn_zsl_check<T, F: Fn(Layout) -> *mut T>(
    layout: Layout,
    f: F
) -> Result<NonNull<u8>, Error> {
    if layout.is_zsl() { Err(Error::ZeroSizedLayout) } else { null_q_dyn(f(layout), layout) }
}
// TODO: lower const msrv and generally improve these. will require some testing regarding effects
//  of current and alternative implementations on provenance
#[::rustversion::since(1.75)]
/// Subtracts `n` bytes from a pointer's address.
///
/// Note that this is only `const` on Rust versions 1.75 and above.
///
/// # Safety
///
/// The caller must ensure:
/// - <code>n < [USIZE_MAX_NO_HIGH_BIT]</code>
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub const unsafe fn byte_sub<T: ?Sized>(p: *const T, n: usize) -> *const T {
    p.byte_sub(n)
}
#[::rustversion::before(1.75)]
/// Subtracts `n` bytes from a pointer's address.
///
/// Note that this is only `const` on Rust versions 1.75 and above.
///
/// # Safety
///
/// The caller must ensure:
/// - <code>n < [USIZE_MAX_NO_HIGH_BIT]</code>
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub unsafe fn byte_sub<T: ?Sized>(p: *const T, n: usize) -> *const T {
    let mut p = p;
    let addr_ptr = (&mut p as *mut *const T).cast::<usize>();
    // SAFETY: the pointer is valid as it is from a &mut.
    unsafe {
        ::core::ptr::write(addr_ptr, *addr_ptr - n);
    }
    p
}

#[::rustversion::since(1.75)]
/// Adds `n` bytes to a pointer's address.
///
/// Note that this is only `const` on Rust versions 1.75 and above.
///
/// # Safety
///
/// The caller must ensure:
/// - <code>n < [USIZE_MAX_NO_HIGH_BIT]</code>
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub const unsafe fn byte_add<T: ?Sized>(p: *const T, n: usize) -> *const T {
    p.byte_add(n)
}
#[::rustversion::before(1.75)]
/// Adds `n` bytes to a pointer's address.
///
/// # Safety
///
/// The caller must ensure:
/// - <code>n < [USIZE_MAX_NO_HIGH_BIT]</code>
/// - the resulting pointer will be within the same allocation as `p`
/// - the resulting pointer's metadata remains valid for the new address
pub unsafe fn byte_add<T: ?Sized>(p: *const T, n: usize) -> *const T {
    let mut p = p;
    let addr_ptr = (&mut p as *mut *const T).cast::<usize>();
    // SAFETY: the pointer is valid as it is from a &mut.
    unsafe {
        ::core::ptr::write(addr_ptr, *addr_ptr + n);
    }
    p
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

    assert_unsafe_precondition!("`union_transmute` requires that `Src::SZ >= Dst::SZ`", <Src, Dst>() => Src::SZ >= Dst::SZ);

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

    assert_unsafe_precondition!(noconst, "`union_transmute` requires that `Src::SZ >= Dst::SZ`", <Src, Dst>() => Src::SZ >= Dst::SZ);

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
