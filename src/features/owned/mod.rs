// TODO: make this align with the MSRV

mod buf;
mod val;
pub(crate) mod into_iter;
// use into_iter::OwnedIter;

pub use buf::*;
pub use val::*;
