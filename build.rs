#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
fn main() {
    let failures = run_checks();
    if failures.is_empty() {
        return;
    }

    for Failure { source, code, msg } in &failures {
        eprintln!("sp_frp UB test {}:{} failed: {}", source, code, msg);
    }

    let example_toolchain = "nightly-x86_64-unknown-linux-gnu 1.91.0 (840b83a10 2025-07-30)";
    let req_info = "please open an issue with your rust toolchain info";
    let get_tc_info = "(`rustup default`, `cargo --version`).";
    panic!(
        "sp_frp UB checks failed (codes: {:?}).\n{} {}\nexample: {}",
        failures.iter().map(|f| f.code).collect::<Vec<_>>(),
        req_info,
        get_tc_info,
        example_toolchain
    );
}

pub struct Failure {
    source: usize,
    code: usize,
    msg: &'static str
}

fn run_checks() -> Vec<Failure> {
    let mut failures = Vec::new();

    failures.extend(checks::sp_frp::check());
    failures.extend(checks::vs_o_s_p_frp::check());

    failures
}

mod checks {
    pub mod sp_frp {
        use {crate::Failure, core::ptr::NonNull};

        pub fn check() -> Vec<Failure> {
            let mut failures = Vec::<Failure>::new();
            let i = 4;

            let mut data: Vec<usize> = (0..i).map(|j| 64 << j).collect();
            let slice: &mut [usize] = &mut data;

            let ptr = slice.as_mut_ptr();
            let len = slice.len();

            let slice_ptr = slice_ptr_from_parts(ptr, len);

            // check that they dereference to the same thing
            if unsafe { &*slice_ptr } != slice {
                failures.push(Failure {
                    source: 0,
                    code: 0,
                    msg: "result doesn't dereference properly"
                });
            }
            // check that they have the same pointer and length
            if slice.as_ptr() != slice_ptr.cast::<usize>() {
                failures.push(Failure {
                    source: 0,
                    code: 1,
                    msg: "result doesn't have the same pointer"
                });
            }
            if unsafe { slice_ptr.as_ref() }.unwrap().len() != len {
                failures.push(Failure {
                    source: 0,
                    code: 2,
                    msg: "result doesn't have the same length"
                });
            }

            unsafe {
                if len
                    != nonnull_slice_len(nonnull_slice_from_parts(
                        NonNull::new_unchecked(ptr),
                        len
                    ))
                {
                    failures.push(Failure {
                        source: 0,
                        code: 3,
                        msg: "result doesn't have the correct metadata"
                    });
                }
            }

            for (i, &elem) in slice.iter().enumerate() {
                let via_raw = unsafe { (&*slice_ptr)[i] };
                // check that the values are all the same
                if elem != via_raw {
                    failures.push(Failure {
                        source: 0,
                        code: 4,
                        msg: "values differ between original slice and raw-slice"
                    });
                }

                // manually check that the values are the same
                if via_raw != 64_usize << i {
                    failures.push(Failure {
                        source: 0,
                        code: 5,
                        msg: "raw-slice value mismatch against expected"
                    });
                }
            }

            failures
        }

        // from the crate

        #[must_use]
        fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
            unsafe { (&*ptr.as_ptr()).len() }
        }

        #[must_use]
        fn nonnull_slice_from_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
            unsafe { NonNull::new_unchecked(slice_ptr_from_parts(p.as_ptr(), len)) }
        }

        #[must_use]
        fn slice_ptr_from_parts<T>(p: *mut T, len: usize) -> *mut [T] {
            unsafe {
                // i hate this so much
                *((&(p, len)) as *const (*mut T, usize)).cast::<*mut [T]>()
            }
        }
    }

    pub mod vs_o_s_p_frp {
        use {
            crate::Failure,
            core::{
                hint::unreachable_unchecked,
                mem::{size_of, size_of_val}
            }
        };

        pub fn check() -> Vec<Failure> {
            let mut failures = Vec::<Failure>::new();

            let sized_val = usize::MAX / 2 / 2 * 3 / 5;
            #[allow(clippy::borrow_as_ptr)]
            let sized_ptr = &sized_val as *const usize as *mut usize;
            let slice = (0..20usize).collect::<Vec<_>>();
            let slice_ptr = slice.as_slice() as *const [usize] as *mut [usize];

            let sized_ptr_remade = anysize_ptr_from_parts::<usize>(sized_ptr.cast::<u8>(), 0);
            let slice_ptr_remade =
                anysize_ptr_from_parts::<[usize]>(slice_ptr.cast::<u8>(), slice.len());

            if sized_ptr_remade != sized_ptr {
                failures.push(Failure {
                    source: 1,
                    code: 0,
                    msg: "result 1 doesn't point to the same sized value"
                });
            }

            let sized_sz = unsafe { size_of_val(&*sized_ptr_remade) };

            if sized_sz != size_of::<usize>() {
                failures.push(Failure {
                    source: 1,
                    code: 1,
                    msg: Box::leak(
                        format!("result 1 doesn't have the correct size: {}", sized_sz)
                            .into_boxed_str()
                    )
                });
            }

            // cast to usize to leave out metadata so that's caught below
            if slice_ptr_remade as *const usize != slice_ptr as *const usize {
                failures.push(Failure {
                    source: 1,
                    code: 2,
                    msg: "result 2 doesn't point to the same unsized slice"
                });
            }

            let unsized_sz = unsafe { size_of_val(&*slice_ptr_remade) };

            if unsized_sz != size_of::<usize>() * slice.len() {
                failures.push(Failure {
                    source: 1,
                    code: 3,
                    msg: Box::leak(
                        format!("result 2 doesn't have the correct size: {}", unsized_sz)
                            .into_boxed_str()
                    )
                });
            }

            failures
        }

        /// Trait for types which are either `VarSized` or `Sized`.
        ///
        /// # Safety
        ///
        /// Implementors must ensure that `T: VarSized` or `T: Sized`.
        pub unsafe trait AnySize {
            /// Whether the type is `Sized` or not.
            const IS_SIZED: bool = false;

            unsafe fn ptr_from_u8_ptr(_p: *mut u8) -> *mut Self {
                unreachable_unchecked()
            }
        }

        unsafe impl<T> AnySize for T {
            const IS_SIZED: bool = true;

            unsafe fn ptr_from_u8_ptr(p: *mut u8) -> *mut T {
                p.cast()
            }
        }

        // unfortunately, we can't use impl<T: VarSized> because it overlaps Sized because Sized and
        //  VarSized are not considered mutually exclusive by the language even though they are.
        unsafe impl<T> AnySize for [T] {}
        unsafe impl AnySize for str {}
        #[cfg(all(feature = "c_str", not(feature = "std")))]
        unsafe impl AnySize for core::ffi::CStr {}
        #[cfg(feature = "std")]
        unsafe impl AnySize for std::ffi::OsStr {}
        #[cfg(feature = "std")]
        unsafe impl AnySize for std::path::Path {}

        /// Creates a *mut T from a `*mut u8` data pointer and `usize` metadata. If `T` is sized,
        /// the metadata is ignored.
        #[must_use]
        #[inline]
        #[allow(clippy::not_unsafe_ptr_arg_deref)]
        pub fn anysize_ptr_from_parts<T: ?Sized + AnySize>(p: *mut u8, meta: usize) -> *mut T {
            if T::IS_SIZED {
                unsafe { T::ptr_from_u8_ptr(p) }
            } else {
                unsafe { make_ptr(p, meta) }
            }
        }

        unsafe fn make_ptr<T: ?Sized>(p: *mut u8, meta: usize) -> *mut T {
            // i hate this so much
            *((&(p, meta)) as *const (*mut u8, usize)).cast::<*mut T>()
        }
    }
}
