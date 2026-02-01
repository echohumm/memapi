#[cfg(feature = "c_alloc")]
/// C heap allocation FFI functions and helpers.
pub mod c_alloc;

#[cfg(feature = "stack_alloc")]
/// C alloca FFI functions and helpers.
pub mod stack_alloc;
