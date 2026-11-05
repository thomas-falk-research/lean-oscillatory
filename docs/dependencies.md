# Dependencies

Lean: Mathlib only (pinned in `lake-manifest.json`; transitive packages are Mathlib's own).
Rust tools: standard library only; `tools/Cargo.lock` lists no crates.
External programs called by the tools: `sha256sum` (coreutils), `git`, `curl`, `openssl` (RFC 3161), `tar` with
`zstd`, `diff`, `bwrap` (bubblewrap, for `lake check` and `lake comparator`).
