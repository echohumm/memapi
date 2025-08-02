// TODO: finish this
// use core::{
//     marker::PhantomData,
//     mem::ManuallyDrop,
//     ptr::NonNull
// };
// use crate::{
//     Alloc,
//     type_props::SizedProps
// };
//
// pub struct OwnedIter<T, A: Alloc> {
//     buf: NonNull<T>,
//     _marker: PhantomData<T>,
//     size: usize,
//     alloc: ManuallyDrop<A>,
//     ptr: NonNull<T>,
//     end: *const T,
// }
//
// impl<T, A: Alloc> Iterator for OwnedIter<T, A> {
//     type Item = T;
//
//     fn next(&mut self) -> Option<T> {
//         let ptr = if T::IS_ZST {
//             if self.ptr.as_ptr() == self.end.cast_mut() {
//                 return None;
//             }
//
//             self.end = self.end.wrapping_byte_sub(1);
//             self.ptr
//         } else {
//             if self.ptr.as_ptr() == self.end.cast_mut() {
//                 return None;
//             }
//
//             let old = self.ptr;
//             self.ptr = unsafe { old.add(1) };
//             old
//         };
//         Some(unsafe { ptr.read() })
//     }
// }
