# t(est)a(ll)m(srv)
import argparse
import itertools
import subprocess
import sys
import os

FEATURES = [
    "std",

    "os_err_reporting",

    "fallible_dealloc",
    "alloc_ext",
    "alloc_slice",
    "resize_in_place",

    "stats",
]

def all_feature_combinations(features):
    for r in range(len(features) + 1):
        for combo in itertools.combinations(features, r):
            yield combo


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

    for combo in all_feature_combinations(FEATURES):
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
            action = "clippy check" if args.clippy else "test"
            print(f"Command failed ({action}, exit code {e.returncode}): {' '.join(cmd)}",
                  file=sys.stderr)
            sys.exit(e.returncode)

    print("All feature combinations completed successfully.")


if __name__ == "__main__":
    main()
