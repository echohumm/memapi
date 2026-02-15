#!/usr/bin/env bash
set -euo pipefail

export MIRIFLAGS=-Zmiri-permissive-provenance
export RUSTDOCFLAGS="-D warnings"

echo "clippy: stable"
cargo +stable clippy -- -D unused_unsafe -D warnings  > /dev/null
echo "clippy: nightly"
cargo +nightly clippy -- -D unused_unsafe -D warnings > /dev/null

# msrv
echo "test: 1.46"
cargo +1.46.0 test --features full_msrv > /dev/null
# random versions ive noticed problems with
echo "test: 1.56"
cargo +1.56.0 test --features full_msrv > /dev/null
echo "test: 1.64"
cargo +1.64.0 test --features full > /dev/null
echo "test: 1.81"
cargo +1.81.0 test --features full_msrv > /dev/null
echo "test: 1.89"
cargo +1.89.0 test --features full_msrv > /dev/null
# main versions
echo "test: stable"
cargo +stable test --features full > /dev/null
echo "test: nightly (miri)"
cargo +nightly miri test --features full_nightly > /dev/null

cargo +nightly doc --features "full_nightly" > /dev/null
