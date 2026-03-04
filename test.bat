@echo off
setlocal

set "MIRIFLAGS=-Zmiri-permissive-provenance"
set "RUSTDOCFLAGS=-D warnings"

echo clippy: stable
set "CARGO_TARGET_DIR=target\stable"
cargo +stable clippy --features "full" -- -D unused_unsafe -D warnings || goto :error

echo clippy: nightly
set "CARGO_TARGET_DIR=target\nightly"
cargo +nightly clippy --features "full_nightly" -- -D unused_unsafe -D warnings || goto :error

echo test: 1.46
set "CARGO_TARGET_DIR=target\1.46"
cargo +1.46.0 test --features "full" || goto :error

echo test: 1.47
set "CARGO_TARGET_DIR=target\1.47"
cargo +1.47.0 test --features "full" || goto :error

echo test: 1.49
set "CARGO_TARGET_DIR=target\1.49"
cargo +1.49.0 test --features "full" || goto :error

echo test: 1.50
set "CARGO_TARGET_DIR=target\1.50"
cargo +1.50.0 test --features "full" || goto :error

echo test: 1.52
set "CARGO_TARGET_DIR=target\1.52"
cargo +1.52.0 test --features "full,__dev" || goto :error

echo test: 1.56
set "CARGO_TARGET_DIR=target\1.56"
cargo +1.56.0 test --features "full,__dev" || goto :error

echo test: 1.57
set "CARGO_TARGET_DIR=target\1.57"
cargo +1.57.0 test --features "full,__dev" || goto :error

echo test: 1.58
set "CARGO_TARGET_DIR=target\1.58"
cargo +1.58.0 test --features "full,__dev" || goto :error

echo test: 1.61
set "CARGO_TARGET_DIR=target\1.61"
cargo +1.61.0 test --features "full,__dev" || goto :error

echo test: 1.64
set "CARGO_TARGET_DIR=target\1.64"
cargo +1.64.0 test --features "full,__dev" || goto :error

echo test: 1.71
set "CARGO_TARGET_DIR=target\1.71"
cargo +1.71.0 test --features "full,__dev" || goto :error

echo test: 1.73
set "CARGO_TARGET_DIR=target\1.73"
cargo +1.73.0 test --features "full,__dev" || goto :error

echo test: 1.75
set "CARGO_TARGET_DIR=target\1.75"
cargo +1.75.0 test --features "full,__dev" || goto :error

echo test: 1.81
set "CARGO_TARGET_DIR=target\1.81"
cargo +1.81.0 test --features "full,__dev" || goto :error

echo test: 1.83
set "CARGO_TARGET_DIR=target\1.83"
cargo +1.83.0 test --features "full,__dev" || goto :error

echo test: 1.89
set "CARGO_TARGET_DIR=target\1.89"
cargo +1.89.0 test --features "full,__dev" || goto :error

echo test: stable
set "CARGO_TARGET_DIR=target\stable"
cargo +stable test --features "full,__dev" || goto :error

echo test: nightly (miri)
set "CARGO_TARGET_DIR=target\nightly"
cargo +nightly miri test --features "full_nightly,__dev" || goto :error

cargo +nightly doc --features "full_nightly,__dev" || goto :error

echo All commands completed successfully.
endlocal
exit /b 0

:error
echo.
echo ERROR: a command failed. See output above.
endlocal
exit /b 1
