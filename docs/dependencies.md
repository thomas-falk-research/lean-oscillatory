<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Dependencies

Lean: Mathlib only (pinned in `lake-manifest.json`; transitive packages are Mathlib's own).
Rust tools in `tools/` (the trust chain): standard library only; `tools/Cargo.lock` lists no crates.
The experimental certificate checker `rust/oscint-cert/` (not part of `make verify-all`) pins five crates in
`rust/oscint-cert/Cargo.toml`: `num-bigint`, `num-integer`, `num-rational`, `num-traits`, `serde_json`.
Python: the tools `tools/*.py` are run with `python3`; hash-pinned requirement files exist for the CI lint step
(`tools/requirements-ci-build.txt`, `tools/requirements-ci.txt`, from `tools/requirements-ci.in`), for `make anchors`
(`tools/requirements-ots.txt`, the OpenTimestamps client) and for the registered hardware experiment
(`experiments/ctqw-chain/hardware/requirements-py312.txt`); the certificate checker `python/oscint_cert` declares no
dependencies (`python/pyproject.toml`).
External programs called by the tools: `sha256sum` (coreutils), `git`, `curl`, `openssl` (RFC 3161), `tar` with
`zstd`, `diff`, `bwrap` (bubblewrap, for `lake check` and `lake comparator`).
