#!/usr/bin/env bash
set -euo pipefail

export MIRIFLAGS=-Zmiri-permissive-provenance
export RUSTDOCFLAGS="-D warnings"

echo "clippy: stable"
CARGO_TARGET_DIR="target/stable" cargo +stable clippy --features "full" -- -D unused_unsafe -D warnings 
echo "clippy: nightly"
CARGO_TARGET_DIR="target/nightly" cargo +nightly clippy --features "full_nightly" -- -D unused_unsafe -D warnings

# msrv
echo "test: 1.46"
CARGO_TARGET_DIR="target/1.46" cargo +1.46.0 test --features "full"
# versions from #[rustversion::since/before/attr] in the crate and random versions i've noticed
#  issues with
echo "test: 1.47"
CARGO_TARGET_DIR="target/1.47" cargo +1.47.0 test --features "full"
echo "test: 1.49"
CARGO_TARGET_DIR="target/1.49" cargo +1.49.0 test --features "full"
echo "test: 1.50"
CARGO_TARGET_DIR="target/1.50" cargo +1.50.0 test --features "full"
echo "test: 1.52"
CARGO_TARGET_DIR="target/1.52" cargo +1.52.0 test --features "full,dev"
echo "test: 1.56"
CARGO_TARGET_DIR="target/1.56" cargo +1.56.0 test --features "full,dev"
echo "test: 1.57"
CARGO_TARGET_DIR="target/1.57" cargo +1.57.0 test --features "full,dev"
echo "test: 1.58"
CARGO_TARGET_DIR="target/1.58" cargo +1.58.0 test --features "full,dev"
echo "test: 1.61"
CARGO_TARGET_DIR="target/1.61" cargo +1.61.0 test --features "full,dev"
echo "test: 1.64"
CARGO_TARGET_DIR="target/1.64" cargo +1.64.0 test --features "full,dev"
echo "test: 1.71"
CARGO_TARGET_DIR="target/1.71" cargo +1.71.0 test --features "full,dev"
echo "test: 1.73"
CARGO_TARGET_DIR="target/1.73" cargo +1.73.0 test --features "full,dev"
echo "test: 1.75"
CARGO_TARGET_DIR="target/1.75" cargo +1.75.0 test --features "full,dev"
echo "test: 1.81"
CARGO_TARGET_DIR="target/1.81" cargo +1.81.0 test --features "full,dev"
echo "test: 1.83"
CARGO_TARGET_DIR="target/1.83" cargo +1.83.0 test --features "full,dev"
echo "test: 1.89"
CARGO_TARGET_DIR="target/1.89" cargo +1.89.0 test --features "full,dev"
# main versions
echo "test: stable"
CARGO_TARGET_DIR="target/stable" cargo +stable test --features "full,dev"
echo "test: nightly (miri)"
CARGO_TARGET_DIR="target/nightly" cargo +nightly miri test --features "full_nightly,dev"

cargo +nightly doc --features "full_nightly,dev"
