use {
    crate::{data::marker::UnsizedCopy, data::type_props::PtrProps},
    core::ptr::{self, NonNull}
};

/// A trait for copying unsized types to uninitialized memory.
pub trait CopyToUninit: UnsizedCopy {
    /// Copies `self` to an uninitialized portion of possibly overlapping memory.
    ///
    /// # Safety
    ///
    /// The caller must ensure `dst` is:
    /// - valid for writes for `self.`[`sz`](PtrProps::sz)`()` bytes.
    /// - properly aligned to `self.`[`aln`](PtrProps::aln)`()`.
    /// - uninitialized, or its data doesn't need to be dropped.
    unsafe fn copy_to(&self, dst: NonNull<u8>) {
        assume!(u_pre
                crate::helpers::ptr_max_align(dst) >= self.aln(),
                "`CopyToUninit::copy_to` requires that `dst` is properly aligned."
        );

        ptr::copy((self as *const Self).cast::<u8>(), dst.as_ptr(), self.sz());
    }

    /// Copies `self` to an uninitialized portion of non-overlapping memory.
    ///
    /// # Safety
    ///
    /// The caller must ensure `dst`:
    /// - is valid for writes for `self.`[`sz`](PtrProps::sz)`()` bytes.
    /// - is properly aligned to `self.`[`aln`](PtrProps::aln)`()`.
    /// - is uninitialized, or its data doesn't need to be dropped.
    /// - doesn't overlap with `self`.
    unsafe fn copy_to_nonoverlapping(&self, dst: NonNull<u8>) {
        assume!(u_pre
            crate::helpers::ptr_max_align(dst) >= self.aln(),
            "`CopyToUninit::copy_to_nonoverlapping` requires that `dst` is properly aligned."
        );
        let sz = self.sz();
        assume!(u_pre
            crate::helpers::check_ptr_overlap(*(&self as *const _ as *const NonNull<u8>), dst, sz),
            "`CopyToUninit::copy_to_nonoverlapping` requires that `self` doesn't overlap with \
            `dst`."
        );

        ptr::copy_nonoverlapping((self as *const Self).cast::<u8>(), dst.as_ptr(), sz);
    }
}

impl<T: ?Sized + UnsizedCopy> CopyToUninit for T {}
