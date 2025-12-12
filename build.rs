#![allow(unknown_lints, clippy::undocumented_unsafe_blocks)]
fn main() {
    let failures = run_checks();
    if failures.is_empty() {
        return;
    }

    for Failure { code, msg } in &failures {
        eprintln!("sp_frp UB test {} failed: {}", code, msg);
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

/// Represents a single check failure
pub struct Failure {
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

            let slice_ptr = slice_ptr_from_raw_parts(ptr, len);

            // check that they dereference to the same thing
            if unsafe { &*slice_ptr } != slice {
                failures.push(Failure { code: 0, msg: "result doesn't dereference properly" });
            }
            // check that they have the same pointer and length
            if slice.as_ptr() != slice_ptr.cast::<usize>() {
                failures.push(Failure { code: 1, msg: "result doesn't have the same pointer" });
            }
            if unsafe { slice_ptr.as_ref() }.unwrap().len() != len {
                failures.push(Failure { code: 2, msg: "result doesn't have the same length" });
            }

            unsafe {
                if len
                    != nonnull_slice_len(nonnull_slice_from_raw_parts(
                        NonNull::new_unchecked(ptr),
                        len
                    ))
                {
                    failures
                        .push(Failure { code: 3, msg: "result doesn't have the correct metadata" });
                }
            }

            for (i, &elem) in slice.iter().enumerate() {
                let via_raw = unsafe { (&*slice_ptr)[i] };
                // check that the values are all the same
                if elem != via_raw {
                    failures.push(Failure {
                        code: 4,
                        msg: "values differ between original slice and raw-slice"
                    });
                }

                // manually check that the values are the same
                if via_raw != 64_usize << i {
                    failures.push(Failure {
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
        fn nonnull_slice_from_raw_parts<T>(p: NonNull<T>, len: usize) -> NonNull<[T]> {
            unsafe { NonNull::new_unchecked(slice_ptr_from_raw_parts(p.as_ptr(), len)) }
        }

        #[must_use]
        fn slice_ptr_from_raw_parts<T>(p: *mut T, len: usize) -> *mut [T] {
            unsafe {
                // i hate this so much
                *((&(p, len)) as *const (*mut T, usize)).cast::<*mut [T]>()
            }
        }
    }

    pub mod vs_o_s_p_frp {
        use {crate::Failure, core::hint::unreachable_unchecked};

        pub fn check() -> Vec<Failure> {
            let mut failures = Vec::<Failure>::new();

            let sized_val = usize::MAX / 2 / 2 * 3 / 5;
            let sized_ptr = &sized_val as *const u8;
            let slice = (0..20usize).collect::<Vec<_>>();
            let slice_ptr = slice.as_slice() as *const [usize] as *const u8;

            if varsized_or_sized_pointer_from_raw_parts(sized_ptr, 0) {

            }

            failures
        }

        /// Trait for types which are either `VarSized` or `Sized`.
        pub unsafe trait VarSizedOrSized {
            /// Whether the type is `Sized` or not.
            const IS_SIZED: bool = false;

            #[doc(hidden)]
            unsafe fn ptr_from_u8_ptr(_p: *mut u8) -> *mut Self {
                unreachable_unchecked()
            }
        }

        unsafe impl<T> VarSizedOrSized for T {
            const IS_SIZED: bool = true;

            #[doc(hidden)]
            unsafe fn ptr_from_u8_ptr(p: *mut u8) -> *mut T {
                p.cast()
            }
        }

        unsafe impl<T> VarSizedOrSized for [T] {}
        unsafe impl VarSizedOrSized for str {}

        /// A pointer to a type that is either `VarSized` or `Sized`.
        pub union VarSizedOrSizedPtr<T: ?Sized + VarSizedOrSized> {
            /// A pointer to a `Sized` type.
            sized: *mut u8,
            /// A pointer to a `VarSized` type. Effectively just `(*mut u8, usize)`
            varsized: *mut T
        }

        impl<T: ?Sized + VarSizedOrSized> VarSizedOrSizedPtr<T> {
            /// Gets the contained pointer.
            pub fn get(&self) -> *mut T {
                if T::IS_SIZED {
                    unsafe { T::ptr_from_u8_ptr(self.sized) }
                } else {
                    unsafe { self.varsized }
                }
            }
        }

        fn varsized_or_sized_pointer_from_raw_parts<T: ?Sized + VarSizedOrSized>(
            p: *mut u8,
            meta: usize
        ) -> VarSizedOrSizedPtr<T> {
            if T::IS_SIZED {
                VarSizedOrSizedPtr { sized: p }
            } else {
                VarSizedOrSizedPtr { varsized: unsafe { make_ptr(p, meta) } }
            }
        }

        unsafe fn make_ptr<T: ?Sized>(p: *mut u8, meta: usize) -> *mut T {
            // i hate this so much
            *((&(p, meta)) as *const (*mut u8, usize)).cast::<*mut T>()
        }
    }
}
