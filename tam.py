# t(est)a(ll)m(srv)
import argparse
import itertools
import subprocess
import sys
import os

FEATURES = [
    "no_alloc",
    "malloc_defaultalloc",

    "std",

    # todo: libc?

    "os_err_reporting",

    "checked_dealloc",
    "alloc_aligned_at",
    "alloc_ext",
    "alloc_slice",
    "resize_in_place",
    "misc_traits",

    "stats",
    "stats_parking_lot",

    "extern_alloc",
    "jemalloc",
    "mimalloc",
    "malloc",
    "mimalloc_err_reporting",
    "mimalloc_global_err",
    "mimalloc_err_output",
]


def all_feature_combinations(features):
    for r in range(len(features) + 1):
        for combo in itertools.combinations(features, r):
            yield combo


def process_feature_combo(combo):
    """Process a feature combination, adding malloc_defaultalloc if no_alloc is present."""
    feature_set = set(combo)

    # If no_alloc is enabled, automatically add malloc_defaultalloc
    if "no_alloc" in feature_set:
        feature_set.add("malloc_defaultalloc")

    return tuple(sorted(feature_set))


def main():
    parser = argparse.ArgumentParser(
        description="Run `cargo +1.56.0 test` or `cargo +1.56.0 clippy` for every combination of features."
    )
    parser.add_argument(
        "-C", "--clippy",
        action="store_true",
        help="Use `clippy -- -D clippy::all -D clippy::pedantic`."
    )
    args = parser.parse_args()

    # Choose the base cargo command
    if args.clippy:
        cargo_cmd = ["cargo", "+1.56.0", "clippy"]
        # clap will pass dashes into the "flags" section after '--'
        extra_args = ["--", "-D", "clippy::all", "-D", "clippy::pedantic", "-D", "clippy::cargo"]
    else:
        cargo_cmd = ["cargo", "+1.56.0", "test"]
        extra_args = []

    env = os.environ.copy()
    env["RUSTFLAGS"] = "-D warnings"

    # Keep track of processed combinations to avoid duplicates
    processed_combos = set()

    for combo in all_feature_combinations(FEATURES):
        # Process the combination (add malloc_defaultalloc if no_alloc is present)
        processed_combo = process_feature_combo(combo)

        # Skip if we've already tested this exact combination
        if processed_combo in processed_combos:
            continue
        processed_combos.add(processed_combo)

        cmd = list(cargo_cmd)
        cmd.append("--no-default-features")
        if processed_combo:
            feature_list = ",".join(processed_combo)
            cmd += ["--features", feature_list]
            print(f"{'Clippy checking' if args.clippy else 'Testing'} features: {feature_list}")
        else:
            print(f"{'Clippy checking' if args.clippy else 'Testing'} with no features")
        cmd += extra_args
        try:
            subprocess.run(cmd, check=True, env=env)
        except subprocess.CalledProcessError as e:
            action = "clippy check" if args.clippy else "test"
            print(f"Command failed ({action}, exit code {e.returncode}): {' '.join(cmd)}",
                  file=sys.stderr)
            sys.exit(e.returncode)

    print("All feature combinations completed successfully.")


if __name__ == "__main__":
    main()
