#!/bin/bash

set -e

# test most recent
cargo test -F owned --no-default-features

# test extra_extra_const with its msrv of 1.83
cargo +1.83.0 test --no-default-features --features="full_min,extra_extra_const"

# test extra_const with its msrv of 1.61
cargo +1.61.0 test --no-default-features --features="full_min,extra_const"

# test base with its msrv of 1.56
cargo +1.56.0 test --no-default-features --features="full_min"
