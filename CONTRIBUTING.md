# Contributing to memapi

Thanks for your interest in contributing! This crate provides a no_std‑friendly memory allocation interface with
optional std and allocator backends. Contributions of all kinds are welcome: bug reports, fixes, features, docs, and
benchmarks.

This document explains how to work on the repository, run checks locally, and open a great pull request.

---

## Ways to contribute

- Report bugs and request features via GitHub Issues: https://github.com/echohumm/memapi/issues
    - Please include your Rust toolchain version (`rustc -V`), OS/arch, relevant feature flags (e.g. `jemalloc`,
      `mimalloc`, `stats`, `std`), and a minimal reproduction if possible.
- Improve docs and examples (README, rustdoc, comments).
- Improve user-facing messages, such as error messages and panic messages.
  - If you need to view error formatting, use the `err_fmt_vw` bin. If it is insufficient, improve it.
- Add tests for uncovered areas and edge cases.
- Implement small, well-scoped improvements or performance wins.

- Tell off the owner for writing bad code, commit messages, etc.

---

## Development setup

- Install Rust via rustup. We aim to compile in as many configuration as possible on the MSRVs stated in the README, but
  develop and test on current stable is fine.
- Clone the repo and work on a topic branch.

---

## Testing matrix and feature flags

Miri (optional):

- For undefined-behavior checks on nightly: `cargo +nightly miri test` (avoid external allocator features when using
  miri).

The preferred way to run tests and clippy checks is using `ta.py` (testall) and `tam.py` (testall-msrv) in the following
configurations:

- `ta.py`: Run all tests in all configurations
- `ta.py -M`: Same, with miri
- `ta.py -C`: Check all configurations with clippy.

Do not skip running `ta.py` in favor of `ta.py -M`. Certain tests are incompatible with miri.

- `tam.py`: Run all MSRV tests in all configurations
- `tam.py -C`: Check all configurations in the MSRV with clippy.

switch to the stable toolchain with `rustup default stable`

- `ta.py -N`: Run all stable tests in all configurations
- `ta.py -N -C`: Check all configurations in the stable toolchain with clippy.

However, letting these commands run to completion would take hours or days, so, running them for ~5 minutes is usually 
fine.

---

## MSRV policy

- Base MSRV is 1.56. Additional features raise MSRV (see README for precise versions: assumptions → 1.57, 
  const_extra/stats_thread_safe_io → 1.61, c_str → 1.64, const_max → 1.83, stats_file_lock → 1.89).
- Do not raise the base MSRV without prior discussion. If a change requires a higher compiler for an optional
  capability, gate it behind a feature and document the new MSRV for that feature.
- Try to preserve compatibility with the listed MSRVs. Always check with `cargo +<version> test/clippy 
  --features="<featureset>"`.

---

## Code style and quality

- Use rustfmt: code must be formatted (`cargo fmt --all`).
- Keep clippy clean: run with `-D warnings` and address lints or explicitly justify them with comments.
- Prefer small, focused changes with clear reasoning and benchmarks where performance is claimed.
- Naming and public API:
    - Favor clarity with existing API patterns and feature naming.
        - If you believe an existing API is confusing, consider renaming it. I know my names are rather poor.
    - Public changes should include docs.

---

## Safety and unsafe code

This crate touches allocation and raw pointers. Any `unsafe` code must include:

- A clear Safety section comment explaining the invariants and why it is sound.
  - If you believe an existing comment is insufficient or unclear, consider updating it.
- Prefer reusing existing helpers/utilities to centralize invariants.
- Tests covering edge cases (ZSTs, alignment, overflow, zeroed/filled paths, grow/shrink, realloc, in-place resize) when
  modifying allocation logic.
- Especially dangerous code should be covered by tests in `tests/potential_ub.rs`
- Code subject to Rust ABI changes should be tested in `build.rs` to verify functionality before even allowing a build.

If `build.rs` does not pass, this is considered a critical issue.

---

## Documentation

- Update rustdoc for all public items you touch. Include a minimal example where helpful.
- Keep README accurate if user-facing behavior or features change.
- If you add feature flags, document them in README and in the crate docs.

---

## Benchmarks

Criterion benches are present under `benches/`.  When claiming performance improvements, please include bench deltas and
environment details.

---

## Changelog

We maintain `CHANGELOG.md` with a manual table of contents and version sections.
For user-facing changes:

- Add an entry under the upcoming section (e.g., “Version X.Y.Z”) or create a new version section if you are
  preparing a release.
- If a commit is the final one of a version, add the date and time in the format "(Y-M-D H:M)" to the version header.
- Keep the format consistent with existing entries and update the Table of Contents anchors.
- Group related bullet points and keep them concise.

---

## Commits and PRs

- Use clear, imperative commit messages: "Fix overflow in grow helper" rather than "fixed".
- Keep PRs focused and small when possible. Explain the problem, the approach, and trade-offs in the description.
- Include tests for bugs fixed or features added.
- Cross-platform and feature-flag awareness is appreciated: mention which feature combos you tested.

PR checklist:

- [ ] Code formatted (`cargo fmt`) and clippy-clean (`ta.py -C`)
- [ ] Runs on specified MSRV
- [ ] All relevant tests pass locally (default and feature-gated where applicable).
- [ ] Documentation updated (rustdoc, README where needed).
- [ ] CHANGELOG.md updated for user-facing changes.
- [ ] Safety comments added/updated for any unsafe code.

---

## License

Any contribution intentionally submitted for inclusion in the work by you shall be dual-licensed as MIT and Apache-2.0,
without any additional terms or conditions. See LICENSE-MIT and LICENSE-APACHE.

Thanks again for contributing to memapi!
