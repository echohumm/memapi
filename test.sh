#!/usr/bin/env bash
set -e

export MIRIFLAGS=-Zmiri-permissive-provenance
export RUSTDOCFLAGS="-D warnings"

echo "clippy: nightly"
cargo +nightly clippy -- -D warnings > /dev/null
echo "clippy: stable"
cargo +stable clippy -- -D warnings  > /dev/null

echo "test: nightly (miri)"
cargo +nightly miri test --features full_nightly > /dev/null
echo "test: stable"
cargo +stable test --features full > /dev/null
echo "test: 1.65"
cargo +1.64.0 test --features full > /dev/null
echo "test: 1.46"
cargo +1.46.0 test --features full_msrv > /dev/null

cargo +nightly doc --features "full_nightly" > /dev/null
