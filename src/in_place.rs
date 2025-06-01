#![allow(missing_docs)]

use crate::{Alloc, AllocError};
use core::alloc::Layout;
use core::ptr::NonNull;

pub trait ResizeInPlace: Alloc {
    // Unlike Alloc::grow, we return a Result<(), AllocError> instead of a
    // Result<NonNull<u8>, AllocError>, because we use the same memory.
    #[track_caller]
    unsafe fn grow_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<(), AllocError>;

    #[track_caller]
    #[inline]
    unsafe fn grow_in_place_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<(), AllocError> {
        self.grow_in_place_filled(ptr, old_layout, new_layout, 0)
    }

    #[track_caller]
    #[inline]
    unsafe fn grow_in_place_patterned<F: Fn(usize) -> u8>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<(), AllocError> {
        self.grow_in_place(ptr, old_layout, new_layout)?;
        let start_num = old_layout.size();
        let start = ptr.add(start_num);
        for i in 0..new_layout.size() - old_layout.size() {
            start.add(i).write(pattern(start_num + i));
        }
        Ok(())
    }

    #[track_caller]
    #[inline]
    unsafe fn grow_in_place_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<(), AllocError> {
        self.grow_in_place(ptr, old_layout, new_layout)?;
        ptr.add(old_layout.size())
            .write_bytes(n, new_layout.size() - old_layout.size());
        Ok(())
    }

    #[track_caller]
    unsafe fn shrink_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<(), AllocError>;

    #[track_caller]
    #[inline]
    unsafe fn realloc_in_place(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<(), AllocError> {
        if new_layout.size() > old_layout.size() {
            self.grow_in_place(ptr, old_layout, new_layout)
        } else {
            self.shrink_in_place(ptr, old_layout, new_layout)
        }
    }

    #[track_caller]
    #[inline]
    unsafe fn realloc_in_place_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<(), AllocError> {
        if new_layout.size() > old_layout.size() {
            self.grow_in_place_zeroed(ptr, old_layout, new_layout)
        } else {
            self.shrink_in_place(ptr, old_layout, new_layout)
        }
    }

    #[track_caller]
    #[inline]
    unsafe fn realloc_in_place_patterned<F: Fn(usize) -> u8>(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        pattern: F,
    ) -> Result<(), AllocError> {
        if new_layout.size() > old_layout.size() {
            self.grow_in_place_patterned(ptr, old_layout, new_layout, pattern)
        } else {
            self.shrink_in_place(ptr, old_layout, new_layout)
        }
    }

    #[track_caller]
    #[inline]
    unsafe fn realloc_in_place_filled(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        n: u8,
    ) -> Result<(), AllocError> {
        if new_layout.size() > old_layout.size() {
            self.grow_in_place_filled(ptr, old_layout, new_layout, n)
        } else {
            self.shrink_in_place(ptr, old_layout, new_layout)
        }
    }
}
