use ::core::{
    fmt::Display,
    result::Result::{self, Err, Ok}
};

#[inline]
#[allow(dead_code)]
fn unwrap_fail<T, E: Display>(r: Result<T, E>) -> T {
    match r {
        Ok(b) => b,
        Err(e) => ::core::panic!("allocation failed: {}", e)
    }
}

pub mod arc;
pub mod boxed;
pub mod rc;
pub mod vec;
