#![allow(clippy::undocumented_unsafe_blocks)]
use {
    crate::{
        DefaultAlloc,
        data::unwrap_fail,
        helpers::{slice_ptr_from_parts, slice_ptr_from_parts_mut},
        layout::Layout,
        traits::{AllocDescriptor, alloc_mut::FullAllocMut, data::type_props::SizedProps}
    },
    ::core::{
        clone::Clone,
        default::Default,
        fmt::{Display, Formatter, Result as FmtResult},
        marker::{PhantomData, Send, Sync},
        ops::{Deref, DerefMut, Drop},
        option::Option::{self, None, Some},
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok},
        todo
    }
};

pub struct Vec<T, A: FullAllocMut = DefaultAlloc> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
    alloc: A,
    _marker: PhantomData<T>
}

pub enum VecErr<A: AllocDescriptor = DefaultAlloc> {
    AllocError(A::Error)
}

impl<A: AllocDescriptor> Display for VecErr<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VecErr::AllocError(e) => Display::fmt(e, f)
        }
    }
}

unsafe impl<T: Send, A: FullAllocMut + Send> Send for Vec<T, A> {}
unsafe impl<T: Sync, A: FullAllocMut + Sync> Sync for Vec<T, A> {}

impl<T> Default for Vec<T> {
    fn default() -> Vec<T> {
        Vec::<T>::new()
    }
}

impl<T> Vec<T> {
    #[must_use]
    pub const fn new() -> Vec<T> {
        Vec::<T>::new_in(DefaultAlloc)
    }

    #[must_use]
    pub fn with_capacity(cap: usize) -> Vec<T> {
        Vec::<T>::with_capacity_in(cap, DefaultAlloc)
    }

    pub fn try_with_capacity(cap: usize) -> Result<Vec<T>, VecErr> {
        Vec::<T>::try_with_capacity_in(cap, DefaultAlloc)
    }
}

impl<T, A: FullAllocMut> Vec<T, A> {
    #[must_use]
    pub const fn new_in(alloc: A) -> Vec<T, A> {
        Vec { ptr: NonNull::dangling(), len: 0, cap: 0, alloc, _marker: PhantomData }
    }

    #[must_use]
    pub fn with_capacity_in(cap: usize, alloc: A) -> Vec<T, A> {
        unwrap_fail(Vec::<T, A>::try_with_capacity_in(cap, alloc))
    }

    pub fn try_with_capacity_in(cap: usize, alloc: A) -> Result<Vec<T, A>, VecErr<A>> {
        let mut alloc = alloc;
        Ok(Vec {
            ptr: tri!(wrap(VecErr::AllocError) alloc.alloc_mut(T::LAYOUT)).cast::<T>(),
            len: 0,
            cap,
            alloc,
            _marker: PhantomData
        })
    }

    pub fn push(&mut self, elem: T) {
        unwrap_fail(self.expand_to_fit(1));
        unsafe {
            self.push_unchecked(elem);
        }
    }

    #[::rustversion::attr(since(1.83), const)]
    pub fn push_within_capacity(&mut self, elem: T) -> Result<(), T> {
        if self.len < self.cap {
            unsafe {
                self.push_unchecked(elem);
            }
            Ok(())
        } else {
            Err(elem)
        }
    }

    #[::rustversion::attr(since(1.83), const)]
    pub unsafe fn push_unchecked(&mut self, elem: T) {
        ptr::write(self.ptr.as_ptr().add(self.len), elem);
        self.len += 1;
    }

    #[::rustversion::attr(since(1.71), const)]
    pub fn pop(&mut self) -> Option<T> {
        if self.len > 0 { Some(unsafe { self.pop_unchecked() }) } else { None }
    }

    #[::rustversion::attr(since(1.71), const)]
    pub unsafe fn pop_unchecked(&mut self) -> T {
        self.len -= 1;
        let ptr = unsafe { self.ptr.as_ptr().add(self.len) };
        unsafe { ptr::read(ptr) }
    }

    pub fn copy_from_slice(&mut self, src: &[T]) {
        todo!()
    }

    pub fn clone_from_slice(&mut self, src: &[T]) {
        todo!()
    }

    pub unsafe fn copy_from_slice_unchecked(&mut self, src: &[T]) {
        todo!()
    }

    pub unsafe fn clone_from_slice_unchecked(&mut self, src: &[T])
    where
        T: Clone
    {
        for elem in src {
            self.push_unchecked(elem.clone());
        }
    }

    pub const fn alloc_layout(&self) -> Layout {
        unsafe { Layout::array_unchecked::<T>(self.cap) }
    }

    pub const fn alloc(&self) -> &A {
        &self.alloc
    }

    pub const fn alloc_mut(&mut self) -> &mut A {
        &mut self.alloc
    }

    pub const fn as_nonnull(&self) -> NonNull<T> {
        self.ptr
    }

    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    pub const fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { &mut *slice_ptr_from_parts_mut(self.ptr.as_ptr(), self.len) }
    }

    pub const fn as_slice(&self) -> &[T] {
        unsafe { &*slice_ptr_from_parts(self.ptr.as_ptr(), self.len) }
    }

    fn expand_to_fit(&mut self, necessary: usize) -> Result<(), VecErr<A>> {
        const fn calc_candidate(cap: usize) -> usize {
            // 1.5x growth factor
            // equivalent to `cap + cap.div_ceil(2)` because its msrv is 1.73
            let half = cap / 2;
            cap + if cap % 2 > 0 { half + 1 } else { half }
        }

        let necessary = self.len + necessary;

        if necessary > self.cap {
            // todo: zero init may be better
            let mut new_cap = calc_candidate(self.cap);
            while new_cap < necessary {
                new_cap = calc_candidate(new_cap);
            }

            let ptr = tri!(wrap(VecErr::AllocError) self.alloc.alloc_mut(T::LAYOUT)).cast::<T>();

            // TODO: may be better if wrapped in non-zero len check
            unsafe {
                ptr::copy_nonoverlapping(self.ptr.as_ptr(), ptr.as_ptr(), self.len);
            }
            // this already does a non-zero len + non-dangling check
            unsafe {
                self.alloc.dealloc_mut(self.ptr.cast(), self.alloc_layout());
            }

            self.ptr = ptr;
            self.cap = new_cap;
        }

        Ok(())
    }
}

impl<T, A: FullAllocMut> Drop for Vec<T, A> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), self.len));
        }
        unsafe { self.alloc.dealloc_mut(self.ptr.cast::<u8>(), self.alloc_layout()) }
    }
}

impl<T, A: FullAllocMut> Deref for Vec<T, A> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, A: FullAllocMut> DerefMut for Vec<T, A> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T: Clone, A: FullAllocMut + Clone> Clone for Vec<T, A> {
    fn clone(&self) -> Vec<T, A> {
        let mut vec: Vec<T, A> = Vec::with_capacity_in(self.len, self.alloc.clone());
        unsafe {
            vec.clone_from_slice_unchecked(self.as_slice());
        }
        vec
    }
}
