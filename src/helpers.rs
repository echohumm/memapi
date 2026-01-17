use {
    crate::{
        Alloc,
        BasicAlloc,
        Layout,
        data::type_props::{PtrProps, SizedProps, VarSized},
        error::{ArithErr, ArithOp, Cause, Error, LayoutErr}
    },
    core::{
        mem::forget,
        ops::Deref,
        ptr::{self, NonNull}
    }
};

/// The maximum value of a `usize` with no high bit.
///
/// Equivalent to <code>[usize::MAX] >> 1</code> or <code>[isize::MAX] as usize</code>.
pub const USIZE_MAX_NO_HIGH_BIT: usize = usize::MAX >> 1;

/// A `usize` in which only the high bit is set.
///
/// Equivalent to <code>[usize::MAX] ^ ([usize::MAX] >> 1)</code>, <code>[usize::MAX] <<
/// [usize::BITS] - 1</code>, or <code>[USIZE_MAX_NO_HIGH_BIT] + 1</code>
pub const USIZE_HIGH_BIT: usize = usize::MAX ^ (USIZE_MAX_NO_HIGH_BIT);

/// A small helper to generate a `usize` in which only the bit at the given index is set.
#[must_use]
#[inline]
pub const fn usize_bit(bit: u8) -> usize {
    USIZE_HIGH_BIT >> bit
}

/// Performs a checked arithmetic operation on two `usize`s.
///
/// Note that this is only `const` on Rust versions 1.47 and above.
///
/// # Errors
///
/// <code>Err([ArithErr]\(l, op, r\))</code> if the requested operation would cause an overflow,
/// underflow, or conversion error.
#[rustversion::attr(since(1.47), const)]
pub fn checked_op(l: usize, op: ArithOp, r: usize) -> Result<usize, ArithErr> {
    #[rustversion::since(1.52)]
    #[allow(clippy::inline_always)]
    #[inline(always)]
    const fn checked_div(l: usize, r: usize) -> Option<usize> {
        l.checked_div(r)
    }
    #[rustversion::before(1.52)]
    const fn checked_div(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l / r) }
    }

    #[rustversion::since(1.52)]
    #[allow(clippy::inline_always)]
    #[inline(always)]
    const fn checked_rem(l: usize, r: usize) -> Option<usize> {
        l.checked_rem(r)
    }
    #[rustversion::before(1.52)]
    const fn checked_rem(l: usize, r: usize) -> Option<usize> {
        if r == 0 { None } else { Some(l % r) }
    }

    #[rustversion::since(1.50)]
    #[allow(clippy::inline_always)]
    #[inline(always)]
    const fn checked_pow(l: usize, r: u32) -> Option<usize> {
        l.checked_pow(r)
    }
    #[rustversion::before(1.50)]
    #[rustversion::attr(since(1.47), const)]
    fn checked_pow(l: usize, mut r: u32) -> Option<usize> {
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
        ArithOp::Rem => checked_rem(l, r),
        ArithOp::Pow if r > u32::MAX as usize => None,
        // cannot be truncated because we check size first
        #[allow(clippy::cast_possible_truncation)]
        ArithOp::Pow => checked_pow(l, r as u32)
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
pub const fn align_up(v: usize, align: usize) -> usize {
    let m1 = align - 1;
    (v + m1) & !m1
}

/// Attempts to align the given value `v` up to the next multiple of `align`.
///
/// # Errors
///
/// - <code>Err([Error::InvalidLayout]\(v, align, [LayoutErr::ZeroAlign]\))</code> if `align == 0`.
/// - <code>Err([Error::InvalidLayout]\(v, align, [LayoutErr::NonPowerOfTwoAlign]\))</code> if
///   `align` is not a power of two.
/// - <code>Err([Error::ArithmeticError]\([ArithErr]\(v, [ArithOp::Add], align - 1\)\)</code> if `v
///   + (align - 1)` would overflow.
#[rustversion::attr(since(1.47), const)]
pub fn round_up_checked(v: usize, align: usize) -> Result<usize, Error> {
    if align == 0 {
        return Err(Error::InvalidLayout(v, align, LayoutErr::ZeroAlign));
    } else if !align.is_power_of_two() {
        return Err(Error::InvalidLayout(v, align, LayoutErr::NonPowerOfTwoAlign));
    }

    // align isn't 0, so align - 1 can't underflow
    let m1 = align - 1;
    Ok(tri!(::ArithmeticError checked_op(v, ArithOp::Add, m1)) & !m1)
}

/// Returns a [`NonNull`] which has the given alignment as its address.
///
/// # Safety
///
/// The caller must ensure `align` is a valid power of two.
#[must_use]
#[inline]
pub const unsafe fn dangling_nonnull(align: usize) -> NonNull<u8> {
    NonNull::new_unchecked(align as *mut u8)
}

/// Returns the maximum alignment satisfied by a non-null pointer.
#[cfg_attr(miri, track_caller)]
#[must_use]
#[inline]
pub fn ptr_max_align(ptr: NonNull<u8>) -> usize {
    let p = ptr.as_ptr() as usize;
    p & p.wrapping_neg()
}

/// Checks if two pointers to data of size `sz` overlap.
#[must_use]
#[inline]
pub fn check_ptr_overlap(a: NonNull<u8>, b: NonNull<u8>, sz: usize) -> bool {
    if sz == 0 {
        return false;
    }

    let a = a.as_ptr() as usize;
    let b = b.as_ptr() as usize;

    if a < b { (b - a) < sz } else { (a - b) < sz }
}

/// Creates a <code>[NonNull]<\[T\]></code> from a pointer and a length.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
///
/// This is a helper used in place of [`NonNull::slice_from_raw_parts`], which was stabilized after
/// this crate's MSRV.
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn nonnull_slice_from_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
    varsized_nonnull_from_parts(p.cast(), len)
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// Note that this is only `const` on Rust versions 1.61 and above.
///
/// This is a helper used in place of [`ptr::slice_from_raw_parts_mut`], which was const-stabilized
/// after this crate's MSRV.
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn slice_ptr_from_parts_mut<T>(p: *mut T, len: usize) -> *mut [T] {
    varsized_ptr_from_parts_mut(p.cast(), len)
}

/// Creates a `*mut [T]` from a pointer and a length.
///
/// Note that this is only `const` on Rust versions 1.47 and above.
#[rustversion::attr(since(1.61), const)]
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
#[rustversion::attr(since(1.58), const)]
#[must_use]
#[inline]
pub unsafe fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    (&*(ptr.as_ptr() as *const [T])).len()
}

/// Creates a dangling, zero-length, [`NonNull`] pointer with the proper alignment.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn varsized_dangling_nonnull<T: ?Sized + VarSized>() -> NonNull<T> {
    // SAFETY: the implementor of VarSized guarantees the ALN is valid.
    varsized_nonnull_from_parts(unsafe { dangling_nonnull(T::ALN) }, 0)
}

/// Creates a dangling, zero-length [`NonNull`] pointer with the proper alignment.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[rustversion::attr(since(1.61), const)]
#[must_use]
pub fn varsized_dangling_ptr<T: ?Sized + VarSized>() -> *mut T {
    // SAFETY: the implementor of VarSized guarantees the ALN is valid.
    varsized_ptr_from_parts_mut(unsafe { dangling_nonnull(T::ALN).as_ptr() }, 0)
}

/// Creates a <code>[NonNull]<T></code> from a pointer and a `usize` size metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[rustversion::attr(since(1.61), const)]
#[must_use]
#[inline]
pub fn varsized_nonnull_from_parts<T: ?Sized + VarSized>(
    p: NonNull<u8>,
    meta: usize
) -> NonNull<T> {
    // SAFETY: `p` was already non-null, so it with different meta must also be nn.
    unsafe { NonNull::new_unchecked(varsized_ptr_from_parts_mut(p.as_ptr(), meta)) }
}

#[rustversion::since(1.83)]
/// Creates a `*mut T` from a pointer and a `usize` size metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[must_use]
#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub const fn varsized_ptr_from_parts_mut<T: ?Sized + VarSized>(p: *mut u8, meta: usize) -> *mut T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe {
        *((&ptr::slice_from_raw_parts_mut::<T::SubType>(p.cast(), meta)
            as *const *mut [T::SubType])
            .cast::<*mut T>())
    }
}
#[rustversion::before(1.83)]
/// Creates a `*mut T` from a pointer and a `usize` size metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[must_use]
#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[rustversion::attr(since(1.61), const)]
pub fn varsized_ptr_from_parts_mut<T: ?Sized + VarSized>(p: *mut u8, meta: usize) -> *mut T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe { crate::helpers::union_transmute::<(*mut u8, usize), *mut T>((p, meta)) }
}

#[rustversion::since(1.64)]
/// Creates a `*mut T` from a pointer and a `usize` size metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[must_use]
#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub const fn varsized_ptr_from_parts<T: ?Sized + VarSized>(p: *const u8, meta: usize) -> *const T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe {
        *((&ptr::slice_from_raw_parts::<T::SubType>(p.cast(), meta)
            as *const *const [T::SubType])
            .cast::<*const T>())
    }
}
#[rustversion::before(1.64)]
/// Creates a `*mut T` from a pointer and a `usize` size metadata.
///
/// Note that this is only `const` on Rust versions 1.61 and above
#[rustversion::attr(since(1.61), const)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[must_use]
#[inline]
pub fn varsized_ptr_from_parts<T: ?Sized + VarSized>(p: *const u8, meta: usize) -> *const T {
    // SAFETY: VarSized trait requires T::Metadata == usize
    unsafe { crate::helpers::union_transmute::<(*const u8, usize), *const T>((p, meta)) }
}

// Allocation/Result helpers

/// Checks layout for being zero-sized, returning an error if it is, otherwise returning the
/// result of `f(layout)`.
///
/// # Errors
///
/// <code>[Error::ZeroSizedLayout]\([layout.dangling()](Layout::dangling)\)</code> if
/// <code>[layout.size()](Layout::size) == 0</code>.
pub fn zsl_check<T, F: Fn(Layout) -> Result<T, Error>>(layout: Layout, f: F) -> Result<T, Error> {
    if layout.size() == 0 { Err(Error::ZeroSizedLayout(layout.dangling())) } else { f(layout) }
}

#[cfg(feature = "os_err_reporting")]
/// Converts a possibly null pointer into a [`NonNull`] result, including os error info.
///
/// # Errors
///
/// <code>Err([Error::AllocFailed]\(layout, [Cause::OSErr]\(oserr\)\)</code>, where `oserr` is the
/// error from [`io::Error::last_os_error`](std::io::Error::last_os_error), if `ptr.is_null()`.
pub fn null_q_oserr<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, Error> {
    if ptr.is_null() {
        Err(Error::AllocFailed(
            layout,
            // SAFETY: last_os_error is guaranteed to return a real os error
            // unfortunately we have to convert oserr -> i32 -> oserr because io::Error is not
            // Copy, and other traits which Cause is.
            Cause::OSErr(unsafe {
                #[allow(clippy::option_if_let_else)]
                match std::io::Error::last_os_error().raw_os_error() {
                    Some(e) => e,
                    None => core::hint::unreachable_unchecked()
                }
            })
        ))
    } else {
        // SAFETY: we just checked that the pointer is non-null
        Ok(unsafe { NonNull::new_unchecked(ptr.cast()) })
    }
}

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
/// Calls either [`null_q`] or [`null_q_oserr`] depending on whether `os_err_reporting` is enabled.
///
/// Currently set to call [`null_q_oserr`].
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, Error> {
    null_q_oserr(ptr, layout)
}

#[cfg(not(feature = "os_err_reporting"))]
/// Calls either [`null_q`] or [`null_q_oserr`] depending on whether `os_err_reporting` is enabled.
///
/// Currently set to call [`null_q`].
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn<T>(ptr: *mut T, layout: Layout) -> Result<NonNull<u8>, Error> {
    null_q(ptr, layout)
}

/// Checks layout for being zero-sized, returning an error if it is, otherwise attempting
/// allocation using `f(layout)`.
#[allow(clippy::missing_errors_doc)]
pub fn null_q_dyn_zsl_check<T, F: Fn(Layout) -> *mut T>(
    layout: Layout,
    f: F
) -> Result<NonNull<u8>, Error> {
    zsl_check(layout, |layout: Layout| null_q_dyn(f(layout), layout))
}

/// Allocates memory, then calls a predicate on a pointer to the memory and an extra piece of data.
///
/// This is intended for initializing the memory and/or mapping the success value to another.
#[allow(clippy::missing_errors_doc)]
pub fn alloc_then<Ret, A: Alloc + ?Sized, E, F: Fn(NonNull<u8>, E) -> Ret>(
    a: &A,
    layout: Layout,
    e: E,
    then: F
) -> Result<Ret, Error> {
    match a.alloc(layout) {
        Ok(ptr) => Ok(then(ptr, e)),
        Err(e) => Err(e)
    }
}

// TODO: lower const msrv and generally improve these. will require some testing regarding effects
//  of current and alternative implementations on provenance
#[rustversion::since(1.75)]
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
#[rustversion::before(1.75)]
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
        ptr::write(addr_ptr, *addr_ptr - n);
    }
    p
}

#[rustversion::since(1.75)]
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
#[rustversion::before(1.75)]
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
        ptr::write(addr_ptr, *addr_ptr + n);
    }
    p
}

#[rustversion::since(1.49)]
/// Transmutes via a `union`. Performs no validity checks.
///
/// Note that this requires both <code>Src: [Copy]</code> and <code>Dst: [Copy]</code> on Rust
/// versions below 1.49, and is only `const` on 1.56 and above.
///
/// # Safety
///
/// The caller must ensure that <code>[Src::SZ] >= [Dst::SZ]</code> and that `src` is a valid `Dst`.
#[rustversion::attr(since(1.56), const)]
pub unsafe fn union_transmute<Src, Dst>(src: Src) -> Dst {
    use core::mem::ManuallyDrop;

    union Either<Src, Dst> {
        src: ManuallyDrop<Src>,
        dst: ManuallyDrop<Dst>
    }

    ManuallyDrop::into_inner(Either { src: ManuallyDrop::new(src) }.dst)
}
#[rustversion::before(1.49)]
/// Transmutes via a `union`. Performs no validity checks.
///
/// Note that this requires both <code>Src: [Copy]</code> and <code>Dst: [Copy]</code> on Rust
/// versions below 1.49, and is only `const` on 1.56 and above.
///
/// # Safety
///
/// The caller must ensure that <code>[Src::SZ] >= [Dst::SZ]</code> and that `src` is a valid `Dst`.
pub unsafe fn union_transmute<Src: Copy, Dst: Copy>(src: Src) -> Dst {
    union Either<Src: Copy, Dst: Copy> {
        src: Src,
        dst: Dst
    }

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

/// A RAII guard that owns a single allocation and ensures it is deallocated unless explicitly
/// released.
///
/// `AllocGuard` wraps a <code>[NonNull]<T></code> pointer and an allocator reference `&A`. When the
/// guard goes out of scope, the underlying memory will be deallocated via the allocator.
///
/// To take ownership of the allocation without deallocating, call
/// [`release`](SliceAllocGuard::release), which returns the raw pointer and prevents the guard
/// from running its cleanup.
///
/// This should be used in any situation where the initialization of a pointer's data may panic.
/// (e.g., initializing via a clone or any other user-implemented method)
///
/// # Examples
///
/// ```
/// # use core::ptr::NonNull;
/// # use memapi2::{helpers::AllocGuard, Layout, Alloc, DefaultAlloc};
/// # let alloc = DefaultAlloc;
/// // Allocate space for one `u32` and wrap it in a guard
/// let layout = Layout::new::<u32>();
/// let mut guard = unsafe { AllocGuard::new(alloc.alloc(layout).unwrap().cast::<u32>(), &alloc) };
///
/// // Initialize the value
/// unsafe { guard.as_ptr().write(123) };
///
/// // If everything is OK, take ownership and prevent automatic deallocation
/// // (commented out for this example as the pointer won't be used)
/// // let raw = guard.release();
/// ```
pub struct AllocGuard<'a, T: ?Sized, A: BasicAlloc + ?Sized> {
    /// The pointer this guard will deallocate on panic.
    ptr: NonNull<T>,
    /// The allocator used to allocate/deallocate `ptr`.
    alloc: &'a A
}

impl<'a, T: ?Sized, A: BasicAlloc + ?Sized> AllocGuard<'a, T, A> {
    /// Creates a new guard from a pointer and a reference to an allocator.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    ///
    /// # Safety
    ///
    /// The caller must ensure `ptr` is a valid, readable, writable pointer allocated using
    /// `alloc`.
    #[rustversion::attr(since(1.61), const)]
    #[inline]
    pub unsafe fn new(ptr: NonNull<T>, alloc: &'a A) -> AllocGuard<'a, T, A> {
        AllocGuard { ptr, alloc }
    }

    /// Initializes the value by writing to the contained pointer.
    ///
    /// Note that this is only `const` on Rust versions 1.83 and above.
    #[rustversion::attr(since(1.83), const)]
    #[cfg_attr(miri, track_caller)]
    #[inline]
    pub fn init(&mut self, elem: T)
    where
        T: Sized
    {
        // SAFETY: new() requires that the pointer is safe to write to
        unsafe {
            ptr::write(self.ptr.as_ptr(), elem);
        }
    }

    /// Releases ownership of the allocation, preventing deallocation, and returns the raw
    /// pointer.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn release(self) -> NonNull<T> {
        let ptr = self.ptr;
        forget(self);
        ptr
    }
}

impl<T: ?Sized, A: BasicAlloc + ?Sized> Drop for AllocGuard<'_, T, A> {
    #[cfg_attr(miri, track_caller)]
    fn drop(&mut self) {
        // SAFETY: new() requires that the pointer is valid.
        let layout = unsafe { self.ptr.layout() };
        // SAFETY: new() requires that the pointer was allocated using the provided allocator
        unsafe {
            self.alloc.dealloc(self.ptr.cast::<u8>(), layout);
        }
    }
}

impl<T: ?Sized, A: BasicAlloc + ?Sized> Deref for AllocGuard<'_, T, A> {
    type Target = NonNull<T>;

    #[inline]
    fn deref(&self) -> &NonNull<T> {
        &self.ptr
    }
}

/// A RAII guard for a heap‐allocated slice that tracks how many elements have been initialized.
///
/// On drop, it will:
/// 1. Run destructors for each initialized element.
/// 2. Deallocate the entire slice of memory.
///
/// Use [`init`](SliceAllocGuard::init) or [`init_unchecked`](SliceAllocGuard::init_unchecked)
/// to initialize elements one by one, [`extend_init`](SliceAllocGuard::extend_init) to
/// initialize many elements at once, and [`release`](SliceAllocGuard::release) to take
/// ownership of the initialized slice without running cleanup.
///
/// # Examples
///
/// ```
/// # extern crate alloc;
/// # use core::ptr::NonNull;
/// # use memapi2::{
/// #  helpers::SliceAllocGuard,
/// #  Alloc,
/// #  DefaultAlloc,
/// #  data::type_props::SizedProps,
/// #  Layout
/// # };
/// # let alloc = DefaultAlloc;
/// # let len = 5;
///
/// let mut guard = unsafe { SliceAllocGuard::new(
///     alloc.alloc(unsafe { Layout::from_size_align_unchecked(u32::SZ * len, u32::ALN) })
///             .unwrap().cast(),
///     &alloc,
///     len
/// ) };
///
/// for i in 0..len {
///     guard.init(i as u32).unwrap();
/// }
///
/// // All elements are now initialized; take ownership:
/// // (commented out for this example as the pointer won't be used)
/// // let slice_ptr = guard.release();
/// ```
pub struct SliceAllocGuard<'a, T, A: BasicAlloc + ?Sized> {
    /// The pointer to the slice which this guard will deallocate on panic.
    ptr: NonNull<T>,
    /// The allocator used to allocate `ptr`.
    alloc: &'a A,
    /// The initialized element count of the slice.
    pub(crate) init: usize,
    /// The allocated length of the slice.
    full: usize
}

impl<'a, T, A: BasicAlloc + ?Sized> SliceAllocGuard<'a, T, A> {
    /// Creates a new slice guard for `full` elements at `ptr` in the given allocator.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `ptr` was allocated using `alloc`, has space for `full`
    /// `T`, and is readable, writable, valid, and aligned.
    #[rustversion::attr(since(1.61), const)]
    #[inline]
    pub unsafe fn new(ptr: NonNull<T>, alloc: &'a A, full: usize) -> SliceAllocGuard<'a, T, A> {
        SliceAllocGuard { ptr, alloc, init: 0, full }
    }

    /// Creates a new slice guard for `full` elements at `ptr` in the given allocator.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    ///
    /// # Safety
    ///
    /// In addition to the restrictions of [`SliceAllocGuard::new`], the caller must ensure
    /// that `init` is the number of existing initialized elements in the slice.
    #[rustversion::attr(since(1.61), const)]
    #[inline]
    pub unsafe fn new_with_init(
        ptr: NonNull<T>,
        alloc: &'a A,
        init: usize,
        full: usize
    ) -> SliceAllocGuard<'a, T, A> {
        SliceAllocGuard { ptr, alloc, init, full }
    }

    /// Release ownership of the slice without deallocating memory, returning a
    /// <code>[NonNull]<T></code> pointer to the slice.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn release(self) -> NonNull<[T]> {
        let ret = self.get_init_part();
        forget(self);
        ret
    }

    /// Release ownership of the slice without deallocating memory, returning a
    /// <code>[NonNull]<T></code> pointer to the slice's first element.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn release_first(self) -> NonNull<T> {
        let ret = self.ptr;
        forget(self);
        ret
    }

    /// Gets a <code>[NonNull]<\[T\]></code> pointer to the initialized elements of the slice.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[cfg_attr(miri, track_caller)]
    #[must_use]
    pub fn get_init_part(&self) -> NonNull<[T]> {
        nonnull_slice_from_parts(self.ptr, self.init)
    }

    /// Gets a <code>[NonNull]<\[T\]></code> pointer to the uninitialized elements of the slice.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    pub fn get_uninit_part(&self) -> NonNull<[T]> {
        // SAFETY: `self.init` will be in bounds unless an init-setting method was used incorrectly.
        let ptr = unsafe { self.ptr.as_ptr().add(self.init) };
        nonnull_slice_from_parts(
            // SAFETY: the pointer was a valid NonNull to begin with, adding cannot invalidate
            //  it.
            unsafe { NonNull::new_unchecked(ptr) },
            self.full - self.init
        )
    }

    /// Gets a <code>[NonNull]<\[T\]></code> pointer to the full slice.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[cfg_attr(miri, track_caller)]
    #[must_use]
    pub fn get_full(&self) -> NonNull<[T]> {
        nonnull_slice_from_parts(self.ptr, self.full)
    }

    /// Sets the initialized element count.
    ///
    /// Note that this is only `const` on Rust versions 1.83 and above.
    ///
    /// # Safety
    ///
    /// The caller must ensure the new count is correct.
    #[rustversion::attr(since(1.83), const)]
    #[inline]
    pub unsafe fn set_init(&mut self, init: usize) {
        self.init = init;
    }

    /// Initializes the next element of the slice with `elem`.
    ///
    /// Note that this is only `const` on Rust versions 1.83 and above.
    ///
    /// # Errors
    ///
    /// `Err(elem)` if there is not enough capacity for another element.
    #[rustversion::attr(since(1.83), const)]
    #[inline]
    pub fn init(&mut self, elem: T) -> Result<(), T> {
        if self.init == self.full {
            return Err(elem);
        }
        // SAFETY: we just verified that there is still space for a new element
        unsafe {
            self.init_unchecked(elem);
        }
        Ok(())
    }

    /// Initializes the next element of the slice with `elem`.
    ///
    /// Note that this is only `const` on Rust versions 1.83 and above.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the slice is not at capacity.
    /// (<code>[self.initialized()](SliceAllocGuard::initialized) <
    /// [self.full()](SliceAllocGuard::full)</code>)
    #[rustversion::attr(since(1.83), const)]
    #[inline]
    pub unsafe fn init_unchecked(&mut self, elem: T) {
        ptr::write(self.ptr.as_ptr().add(self.init), elem);
        self.init += 1;
    }

    /// Returns how many elements have been initialized.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn initialized(&self) -> usize {
        self.init
    }

    /// Returns the total number of elements in the slice.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn full(&self) -> usize {
        self.full
    }

    /// Returns `true` if every element in the slice has been initialized.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn is_full(&self) -> bool {
        self.init == self.full
    }

    /// Returns `true` if no elements have been initialized.
    ///
    /// Note that this is only `const` on Rust versions 1.61 and above.
    #[rustversion::attr(since(1.61), const)]
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.init == 0
    }

    /// Copies as many elements from `slice` as will fit.
    ///
    /// On success, all elements are copied and `Ok(())` is returned. If
    /// `slice.len() > remaining_capacity`, it copies as many elements as will fit, advances the
    /// initialized count to full, and returns `Err(excess)`.
    ///
    /// Note that this is only `const` on Rust versions 1.83 and above.
    ///
    /// # Errors
    ///
    /// `Err(excess)` if some elements could not be copied from the slice due to a lack of
    /// capacity.
    #[rustversion::attr(since(1.83), const)]
    pub fn copy_from_slice(&mut self, slice: &[T]) -> Result<(), usize>
    where
        T: Copy
    {
        let lim = self.full - self.init;
        let to_copy = if slice.len() < lim { slice.len() } else { lim };

        // SAFETY: `self.init` will be in bounds unless an init-setting method was used incorrectly.
        let uninit_p = unsafe { self.ptr.as_ptr().add(self.init) };

        // SAFETY: to_copy will be at most the remaining space after uninit_p, so it won't go oob.
        unsafe {
            ptr::copy(slice.as_ptr(), uninit_p, to_copy);
        }

        self.init += to_copy;
        let uncopied = slice.len() - to_copy;
        if uncopied == 0 { Ok(()) } else { Err(uncopied) }
    }

    /// Clones as many elements from `slice` as will fit.
    ///
    /// On success, all elements are cloned and `Ok(())` is returned. If
    /// `slice.len() > remaining_capacity`, it clones as many elements as will fit, advances the
    /// initialized count to full, and returns `Err(excess)`.
    ///
    /// # Errors
    ///
    /// `Err(excess)` if some elements could not be cloned due to a lack of capacity.
    pub fn clone_from_slice(&mut self, slice: &[T]) -> Result<(), usize>
    where
        T: Clone
    {
        let lim = self.full - self.init;
        let to_clone = if slice.len() < lim { slice.len() } else { lim };

        // SAFETY: `self.init` and `to_clone` will disallow oob access unless there was improper
        //  usage of unsafe setter methods
        for elem in &slice[..to_clone] {
            // SAFETY: `self.init` will be in bounds unless an init-setting method was used
            //  incorrectly.
            let ptr = unsafe { self.as_ptr().add(self.init) };
            // SAFETY: `ptr` is valid. we have not yet incremented `self.init`, so `drop` won't
            //  access uninitialized memory if cloning fails.
            unsafe {
                ptr::write(ptr, elem.clone());
            }
            self.init += 1;
        }

        self.init += to_clone;
        let uncloned = slice.len() - to_clone;
        if uncloned == 0 { Ok(()) } else { Err(uncloned) }
    }

    /// Initializes the next elements of the slice with the elements from `iter`.
    ///
    /// # Errors
    ///
    /// `Err(iter)` if the slice ran out of capacity before the iterator ran out of elements. The
    /// returned iterator will be partially or fully consumed.
    pub fn extend_init<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), I::IntoIter> {
        let mut iter = iter.into_iter();
        loop {
            if self.init == self.full && iter.size_hint().0 != 0 {
                return Err(iter);
            }
            match iter.next() {
                Some(elem) => {
                    // SAFETY: we just verified that there is space
                    let uninit_ptr = unsafe { self.ptr.as_ptr().add(self.init) };
                    // SAFETY: the pointer is valid, and we just verified that there is space.
                    unsafe {
                        ptr::write(uninit_ptr, elem);
                        self.init += 1;
                    }
                }
                None => return Ok(())
            }
        }
    }
}

impl<T, A: BasicAlloc + ?Sized> Drop for SliceAllocGuard<'_, T, A> {
    fn drop(&mut self) {
        // SAFETY: `self.init` will be correct without improper usage of methods which set it.
        unsafe {
            ptr::drop_in_place(slice_ptr_from_parts_mut(self.ptr.as_ptr(), self.init));
        }
        // SAFETY: this memory was already allocated with this layout, so its size and align must be
        // valid.
        let layout = unsafe { Layout::from_size_align_unchecked(T::SZ * self.full, T::ALN) };
        // SAFETY: new() requires that the pointer was allocated using the provided allocator.
        unsafe {
            self.alloc.dealloc(self.ptr.cast(), layout);
        }
    }
}

impl<T, A: BasicAlloc + ?Sized> Deref for SliceAllocGuard<'_, T, A> {
    type Target = NonNull<T>;

    #[inline]
    fn deref(&self) -> &NonNull<T> {
        &self.ptr
    }
}
