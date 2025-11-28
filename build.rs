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
        fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize { unsafe { (&*ptr.as_ptr()).len() } }

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
}
