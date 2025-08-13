# t(est)a(ll)
import argparse
import itertools
import subprocess
import sys
import os

FEATURES = [
    "nightly",
    "std",

    "libc",

    "os_err_reporting",

    "const_extras",
    "const_max",
    "c_str",

    "metadata",
    "clone_to_uninit",
    "specialization",
    "sized_hierarchy",

    "fallible_dealloc",
    "alloc_aligned_at",
    "alloc_ext",
    "alloc_slice",
    "resize_in_place",

    "stats",
    "stats_file_lock",
    "stats_parking_lot",

    "extern_alloc",
    "jemalloc",
    "mimalloc",
    "mimalloc_err_reporting",
    "mimalloc_err_output",
]

NIGHTLY_FEATURES = {
    "nightly",
    "metadata",
    "sized_hierarchy",
    "clone_to_uninit",
    "specialization",
}

def all_feature_combinations(features):
    for r in range(len(features) + 1):
        for combo in itertools.combinations(features, r):
            yield combo


def main():
    parser = argparse.ArgumentParser(
        description="Run `cargo test`, `cargo miri test`, or `cargo clippy` for every combination of features."
    )
    parser.add_argument(
        "-M", "--miri",
        action="store_true",
        help="Use `cargo miri test` instead of `cargo test`."
    )
    parser.add_argument(
        "-C", "--clippy",
        action="store_true",
        help="Use `cargo clippy -- -D clippy::all -D clippy::pedantic`."
    )
    parser.add_argument(
        "-N", "--no-nightly",
        action="store_true",
        help="Skip any combinations that include nightly-only features"
    )
    args = parser.parse_args()

    if args.miri and args.clippy:
        parser.error("Cannot use both --miri and --clippy")

    # Choose the base cargo command
    if args.clippy:
        cargo_cmd = ["cargo", "clippy"]
        # clap will pass dashes into the "flags" section after '--'
        extra_args = ["--", "-D", "clippy::all", "-D", "clippy::pedantic", "-D", "clippy::cargo", "-A",
                      "clippy::redundant_feature_names"]
    else:
        cargo_cmd = ["cargo", "miri", "test"] if args.miri else ["cargo", "test"]
        extra_args = []

    # Prepare environment with RUSTFLAGS
    env = os.environ.copy()
    env["RUSTFLAGS"] = "-D warnings"

    for combo in all_feature_combinations(FEATURES):
        if args.no_nightly and any(f in NIGHTLY_FEATURES for f in combo):
            continue

        cmd = list(cargo_cmd)
        cmd.append("--no-default-features")
        if combo:
            feature_list = ",".join(combo)
            cmd += ["--features", feature_list]
            print(f"{'Clippy checking' if args.clippy else 'Testing'} features: {feature_list}")
        else:
            print(f"{'Clippy checking' if args.clippy else 'Testing'} with no features")
        cmd += extra_args
        try:
            subprocess.run(cmd, check=True, env=env)
        except subprocess.CalledProcessError as e:
            action = "clippy check" if args.clippy else ("miri test" if args.miri else "test")
            print(f"Command failed ({action}, exit code {e.returncode}): {' '.join(cmd)}",
                  file=sys.stderr)
            sys.exit(e.returncode)

    print("All feature combinations completed successfully.")


if __name__ == "__main__":
    main()
