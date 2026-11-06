# OscInt

A Lean 4 + Mathlib library of uniform oscillatory-integral estimates in one and two variables with explicit
constants: van der Corput (S1), nondegenerate stationary phase uniform in a linear term (S2), the uniform fold
estimate m^{-5/6} (S3), and the uniform D4 estimate t^{-2/3} with its limit constant (S4).
Lean package `OscInt`; toolchain v4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag v4.35.0).

## Status

| Statement | Status |
|---|---|
| S1 1D van der Corput | machine-checked as stated (`OscInt.vanDerCorput_one/two/three`); proof ported from roos-j/lean-oscillatory (Roos–Praveen, Mathlib PR #39406), see `docs/STATUS.md` |
| S2 stationary phase (S2.1 non-stationary, S2.2 nondegenerate) | machine-checked as stated (`OscInt.nonStationary`, `OscInt.stationaryPhase`), see `docs/STATUS.md` |
| S3 fold | machine-checked as stated (`OscInt.fold`; fold condition required on all of K) |
| S4 D4 | not started |

"As stated" means the hypotheses in `docs/statements.md` (derivatives continuous up to the endpoints, as in the
source's C^k assumption). Details and evidence: `docs/STATUS.md`.

## Re-check

Needs elan, Rust ≥ 1.97, `bubblewrap`, `zstd`, `openssl`, `curl`.

```bash
lake exe cache get
make verify-all
```

`verify-all` runs: `verify-toolchain` (hash pins; installed toolchain byte-identical to the pinned archive),
`tools-test`, `guard` (forbidden tokens, statement pins), `lean` (build; axiom audit N/N against the guard's
theorem count; statement-type check; Mathlib name check), `lean-replay` (`leanchecker` per module; export
re-checked by Lean's kernel, its paranoid mode, nanoda, con-leche, con-ron and, via `lake check --paranoid`,
lean4lean), `commit` (statement commitments from the environment and from the export must agree),
`comparator` (frozen challenge, hash-checked against the stamp), `stamp-verify`. It prints PASS, FAIL, or
INCOMPLETE when a step had nothing to check; INCOMPLETE is never reported as PASS.

## What stays trusted

- Lean's kernel and the v4.35.0 toolchain archive, from which every checker above comes (one trust source until a
  checker is built from source at a pinned commit).
- The Mathlib binary cache for the proofs: a source build (CI run 18) reproduced the statement commitments, but
  the replay still uses cache-built `.olean` files (`docs/toolchain.md`).
- The fidelity readings of statements: AI referees, no human reviewer yet.
- The roots of the three RFC 3161 timestamp authorities (`stamps/roots/`); the FreeTSA root is trust on first use.

## Layout

`OscInt/` library; `OscInt/Statements/` frozen statements; `Blueprint/` intermediate propositions; `Challenge/`
`sorry` theorems over the statement module for `lake comparator` (never imported; the challenge is frozen by the
stamped export hash and the pinned statement-file hashes, `stamps/pins.txt`); `Axioms.lean`, `StatementTypes.lean`,
`MathlibNames.lean` checks; `tools/` Rust binaries (std only) and the Lean commitment producer; `docs/`;
`review/` referee reports; `stamps/` timestamp records.

Code: Apache-2.0 (`LICENSE`). Documentation: CC BY 4.0 (`LICENSE-docs`). Citation: `CITATION.cff`.
