#!/usr/bin/env python3
import subprocess
import sys
import os

def run(cmd, **kwargs):
    print(f"> Running: {' '.join(cmd)}")
    # noinspection PyArgumentList
    subprocess.run(cmd, check=True, **kwargs)

def main():
    # locate testall.py next to this script
    here = os.path.dirname(os.path.abspath(__file__))
    testall = os.path.join(here, "testall.py")

    try:
        # 1) set default toolchain to stable
        run(["rustup", "default", "stable"])

        # 2) run testall.py with -C -N
        run([sys.executable, testall, "-C", "-N"])

        # 3) run testall.py with -N
        run([sys.executable, testall, "-N"])

        # 4) switch default back to nightly
        run(["rustup", "default", "nightly"])

        # 5) run testall.py with -C
        run([sys.executable, testall, "-C"])

        # 6) run testall.py with -M
        run([sys.executable, testall, "-M"])

        print("All runs completed successfully.")
    except subprocess.CalledProcessError as e:
        print(f"Step failed (exit code {e.returncode}): {e.cmd}", file=sys.stderr)
        sys.exit(e.returncode)

if __name__ == "__main__":
    main()
