#!/usr/bin/env bash
set -euo pipefail

# Lightweight, safer benchmarking wrapper for Criterion on a primary workstation.
# - Minimizes noise (cache, IO priority, CPU affinity) without heavy system changes.
# - Restores CPU governors on exit.
#
# Usage:
#   BENCH_CPUS="0" BENCH_RUSTFLAGS="-C target-cpu=native" ./bench.sh [cargo-bench-args...]
#
# Environment variables:
#   BENCH_CPUS     - CPU list for taskset (e.g. "0" or "0,1"). Default: "0".
#   BENCH_RUSTFLAGS- Extra RUSTFLAGS. Default: ""

BENCH_CPUS="${BENCH_CPUS:-4,5}"
BENCH_RUSTFLAGS="${BENCH_RUSTFLAGS:-}"
TMP_GOV="$(mktemp)"

cleanup() {
  # restore governors if we saved any
  if [ -f "${TMP_GOV}" ]; then
    while IFS=: read -r cpu gov; do
      govfile="/sys/devices/system/cpu/${cpu}/cpufreq/scaling_governor"
      if [ -w "${govfile}" ]; then
        echo "${gov}" | sudo tee "${govfile}" >/dev/null
      fi
    done < "${TMP_GOV}"
    rm -f "${TMP_GOV}"
  fi
}
trap cleanup EXIT INT TERM

# 1) Refresh sudo timestamp so later sudo operations don't prompt mid-run (best-effort).
sudo -v

# 2) If cpufreq controls exist, save current governors and set "performance".
for cpu_dir in /sys/devices/system/cpu/cpu[0-9]*; do
  govfile="${cpu_dir}/cpufreq/scaling_governor"
  if [ -f "${govfile}" ]; then
    cpu="$(basename "${cpu_dir}")"
    current="$(cat "${govfile}" 2>/dev/null || echo unknown)"
    printf '%s:%s\n' "${cpu}" "${current}" >> "${TMP_GOV}"
    # try to set performance; ignore failures
    echo performance | sudo tee "${govfile}" >/dev/null
  fi
done

# 3) Flush filesystems & drop caches (best-effort).
sudo sync
# writing to drop_caches requires root; do via sudo sh -c
sudo sh -c 'echo 3 > /proc/sys/vm/drop_caches'

# 4) Run cargo bench pinned to chosen CPUs and with elevated IO priority.
#    - taskset pins CPU affinity (reduces scheduling variance).
#    - ionice reduces IO interference.
#    - export RUSTFLAGS so the bench run and benchmarks use target-cpu; allow override.
export RUSTFLAGS="${BENCH_RUSTFLAGS}"
cmd=(sudo nice -n -20 ionice -c1 -n0 taskset -c "${BENCH_CPUS}" sudo -u $USER cargo bench $@)

# Print what we're running (concise).
echo "Running: ${cmd[*]}"
# Run and capture exit code (so trap runs).
"${cmd[@]}"; exit_code=$?

# cleanup() will be called via trap; but call explicitly if not yet done.
cleanup

exit ${exit_code}