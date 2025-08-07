#!/bin/bash

set -e

# test extra_extra_const with its msrv of 1.83, as well as external_allocs_in_place (msrv 1.63)
cargo +1.83.0 test --no-default-features --features="full_min,extra_extra_const,external_allocs_in_place"

# test external_allocs_in_place with its msrv of 1.63
cargo +1.63.0 test --no-default-features --features="full_min,external_allocs_in_place"

# test extra_const with its msrv of 1.61
cargo +1.61.0 test --no-default-features --features="full_min,extra_const"

# test base with its msrv of 1.56
cargo +1.56.0 test --no-default-features --features="full_min"
