use {
    crate::{
        DefaultAlloc,
        error::Error,
        traits::{
            AllocDescriptor,
            alloc_mut::BasicAllocMut,
            data::{
                marker::UnsizedCopy,
                type_props::{PtrProps, SizedProps, VarSized, varsized_nonnull_from_parts}
            }
        }
    },
    ::core::{
        convert::From,
        default::Default,
        fmt::{Debug, Display, Formatter, Result as FmtResult},
        marker::{PhantomData, Send, Sized, Sync},
        mem::MaybeUninit,
        ops::{Deref, DerefMut, Drop},
        panic,
        ptr::{self, NonNull},
        result::Result::{self, Err, Ok},
        write
    }
};

#[inline]
fn unwrap_fail<T: ?Sized, A: BasicAllocMut, E: Display>(r: Result<Box<T, A>, E>) -> Box<T, A> {
    match r {
        Ok(b) => b,
        Err(e) => panic!("allocation for `Box` failed: {}", e)
    }
}

pub struct Box<T: ?Sized, A: BasicAllocMut = DefaultAlloc> {
    ptr: NonNull<T>,
    alloc: A,
    _marker: PhantomData<T>
}

pub enum BoxErr<E: Debug + Display + From<Error>> {
    AllocError(E),
    NullPtr,
    DanglingPtr(*const ())
}

unsafe impl<T: Send, A: BasicAllocMut + Send> Send for Box<T, A> {}
unsafe impl<T: Sync, A: BasicAllocMut + Sync> Sync for Box<T, A> {}

impl<E: Debug + Display + From<Error>> Display for BoxErr<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            BoxErr::AllocError(e) => Display::fmt(e, f),
            BoxErr::NullPtr => write!(f, "received a null pointer"),
            BoxErr::DanglingPtr(ptr) => write!(f, "dangling pointer: {ptr:p} ({ptr:?})", ptr = ptr)
        }
    }
}

impl<T: Default, A: BasicAllocMut + Default> Default for Box<T, A> {
    fn default() -> Box<T, A> {
        Box::new_in(T::default(), A::default())
    }
}

impl<T> Box<T> {
    // TODO: must_use, more new_uninits, new_zeroed
    pub fn new(data: T) -> Box<T> {
        Box::new_in(data, DefaultAlloc)
    }
    #[must_use]
    pub fn new_uninit() -> Box<MaybeUninit<T>> {
        Box::new_uninit_in(DefaultAlloc)
    }

    pub fn try_new(data: T) -> Result<Box<T>, BoxErr<Error>> {
        Box::try_new_in(data, DefaultAlloc)
    }
    pub fn try_new_uninit() -> Result<Box<MaybeUninit<T>>, BoxErr<Error>> {
        Box::try_new_uninit_in(DefaultAlloc)
    }
}

impl<T, A: BasicAllocMut> Box<T, A> {
    pub fn new_in(data: T, alloc: A) -> Box<T, A> {
        unwrap_fail(Box::try_new_in(data, alloc))
    }
    pub fn new_uninit_in(alloc: A) -> Box<MaybeUninit<T>, A> {
        unwrap_fail(Box::try_new_uninit_in(alloc))
    }

    pub fn try_new_in(
        data: T,
        alloc: A
    ) -> Result<Box<T, A>, BoxErr<<A as AllocDescriptor>::Error>> {
        let mut alloc = alloc;
        let ptr = tri!(wrap(BoxErr::AllocError) alloc.alloc_mut(T::LAYOUT)).cast();
        unsafe {
            ptr::write(ptr.as_ptr(), data);
        }
        Ok(Box { ptr, alloc, _marker: PhantomData })
    }
    pub fn try_new_uninit_in(
        alloc: A
    ) -> Result<Box<MaybeUninit<T>, A>, BoxErr<<A as AllocDescriptor>::Error>> {
        let mut alloc = alloc;
        let ptr = tri!(wrap(BoxErr::AllocError) alloc.alloc_mut(T::LAYOUT)).cast();
        Ok(Box { ptr, alloc, _marker: PhantomData })
    }
}

impl<T: ?Sized> Box<T> {
    #[allow(clippy::must_use_candidate)]
    pub const unsafe fn from_raw(ptr: NonNull<T>) -> Box<T> {
        Box::from_raw_in(ptr, DefaultAlloc)
    }

    pub fn copy_from_ref(r: &T) -> Box<T>
    where
        T: UnsizedCopy + VarSized
    {
        Box::copy_from_ref_in(r, DefaultAlloc)
    }

    pub fn try_copy_from_ref(r: &T) -> Result<Box<T>, BoxErr<Error>>
    where
        T: UnsizedCopy + VarSized
    {
        Box::try_copy_from_ref_in(r, DefaultAlloc)
    }

    pub unsafe fn copy_from_ptr(p: *const T) -> Box<T>
    where
        T: UnsizedCopy + VarSized
    {
        unsafe { Box::copy_from_ptr_in(p, DefaultAlloc) }
    }

    pub unsafe fn try_copy_from_ptr(p: *const T) -> Result<Box<T>, BoxErr<Error>>
    where
        T: UnsizedCopy + VarSized
    {
        unsafe { Box::try_copy_from_ptr_in(p, DefaultAlloc) }
    }
}

impl<T: ?Sized, A: BasicAllocMut> Box<T, A> {
    pub const unsafe fn from_raw_in(ptr: NonNull<T>, alloc: A) -> Box<T, A> {
        Box { ptr, alloc, _marker: PhantomData }
    }

    pub fn copy_from_ref_in(r: &T, alloc: A) -> Box<T, A>
    where
        T: UnsizedCopy + VarSized
    {
        unwrap_fail(Box::try_copy_from_ref_in(r, alloc))
    }

    pub fn try_copy_from_ref_in(
        r: &T,
        alloc: A
    ) -> Result<Box<T, A>, BoxErr<<A as AllocDescriptor>::Error>>
    where
        T: UnsizedCopy + VarSized
    {
        unsafe { Box::try_copy_from_ptr_in(r, alloc) }
    }

    pub unsafe fn copy_from_ptr_in(p: *const T, alloc: A) -> Box<T, A>
    where
        T: UnsizedCopy + VarSized
    {
        unwrap_fail(unsafe { Box::try_copy_from_ptr_in(p, alloc) })
    }

    pub unsafe fn try_copy_from_ptr_in(
        p: *const T,
        alloc: A
    ) -> Result<Box<T, A>, BoxErr<<A as AllocDescriptor>::Error>>
    where
        T: UnsizedCopy + VarSized
    {
        let mut alloc = alloc;

        let sz = unsafe { p.sz() };
        let ptr = tri!(wrap(BoxErr::AllocError) alloc.alloc_mut(p.layout()));

        unsafe {
            ptr::copy_nonoverlapping(p.cast::<u8>(), ptr.as_ptr(), sz);
        }
        Ok(Box { ptr: varsized_nonnull_from_parts(ptr, sz), alloc, _marker: PhantomData })
    }
}

impl<T: ?Sized, A: BasicAllocMut> Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl<T: ?Sized, A: BasicAllocMut> DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr.as_ptr() }
    }
}

impl<T: ?Sized, A: BasicAllocMut> Drop for Box<T, A> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.ptr.as_ptr());
        }
        let layout = unsafe { self.ptr.layout() };
        unsafe {
            self.alloc.dealloc_mut(self.ptr.cast(), layout);
        }
    }
}
