# OscInt

[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--9478--6061-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0001-9478-6061)

Author: Thomas Falk III ([ORCID 0009-0001-9478-6061](https://orcid.org/0009-0001-9478-6061)). Cite via `CITATION.cff`.

A Lean 4 + Mathlib library of uniform oscillatory-integral estimates in one and two variables: van der Corput with
explicit constants (S1), nondegenerate stationary phase uniform in a linear term (S2), the uniform fold
estimate m^{-5/6} (S3), and the uniform D4 estimate t^{-2/3} (S4.1, S4.1′), the limit t^{2/3}∫e^{itφ}A → c_C A(0) with a Gamma-free c_C (S4.2) and c_C > 0 (S4.3); the
closed form of c_C (S4.4) is stated, not yet proved.
Lean package `OscInt`; toolchain v4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag v4.35.0).

## Status

| Statement | Status |
|---|---|
| S1 1D van der Corput | machine-checked as stated (`OscInt.vanDerCorput_one/two/three`); proof ported from roos-j/lean-oscillatory (Roos–Praveen, Mathlib PR #39406), see `docs/STATUS.md` |
| S2 stationary phase (S2.1 non-stationary, S2.2 nondegenerate) | machine-checked as stated (`OscInt.nonStationary`, `OscInt.stationaryPhase`), see `docs/STATUS.md` |
| S3 fold | machine-checked as stated (`OscInt.fold`; fold condition required on all of K) |
| S4.1 uniform D4 bound (hyperbolic umbilic D4⁺, `disc < 0`, as the brief) | machine-checked as stated (`OscInt.d4Bound`), see `docs/STATUS.md` |
| S4.1′ uniform D4 bound, both umbilics (`disc ≠ 0`) | machine-checked as stated (`OscInt.d4BoundNe`) |
| S4.2 D4 limit with the Gamma-free c_C | machine-checked as stated (`OscInt.d4Limit`) |
| S4.3 c_C > 0 (alternating series, no Gamma) | machine-checked as stated (`OscInt.d4ConstantPos`; Gamma-free by name, `GammaFree.lean`) |
| S4.4 closed forms of c_C (the brief's Γ(1/3)²/(√3\|Disc\|^{1/6})) | stated and reviewed; not proved. The brief's limit with its constant is S4.2 ∧ S4.4 |

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

- Lean's kernel and the v4.35.0 toolchain archive, from which every local checker above comes. In CI one checker,
  nanoda (`nanoda_lib` 0.4.31 at commit `8de7e0c`), is additionally built from source on a fresh runner and run on the
  same export (`docs/toolchain.md`).
- The Mathlib binary cache for the proofs: a source build (CI run 18) reproduced the statement commitments, but
  the replay still uses cache-built `.olean` files (`docs/toolchain.md`).
- The fidelity readings of statements: AI referees, no human reviewer yet.
- The newest line of `stamps/pins.txt` is written after the stamp it pins, so no timestamp covers it; its
  integrity rests on git history.
- The roots of the three RFC 3161 timestamp authorities (`stamps/roots/`); the FreeTSA root is trust on first use.

## Layout

- `OscInt/` library: `OscInt/Statements/` frozen statements, `OscInt/VanDerCorput/` (S1),
  `OscInt/StationaryPhase/` (S2, S3), `OscInt/D4/` (S4).
- `Blueprint/` intermediate propositions (definitions only); `Challenge/` `sorry` theorems over the statement modules
  for `lake comparator` (never imported; frozen by the stamped export hash and the pinned statement-file hashes,
  `stamps/pins.txt`); one `comparator*.json` per milestone.
- Checks run by `make lean`: `Axioms.lean` (axiom audit), `StatementTypes.lean` (final types are the frozen
  constants), `MathlibNames.lean` (names the plan relies on), `GammaFree.lean` (S4.3 proof method).
- `tools/` Rust binaries (std only) and the Lean commitment producer; `numerics/` floating-point probes (tooling,
  never evidence); `stamps/` timestamp records; `review/` referee reports and prompts (`review/README.md`).

## Documents

| File | Content |
|---|---|
| `docs/statements.md` | the mathematics of every statement, with dated clarifications |
| `docs/STATUS.md` | evidence-derived status per statement |
| `docs/HANDOFF.md` | state and next steps for the next session |
| `docs/ROADMAP.md` | the path to a production-ready library, as a checklist |
| `docs/proof-S2S3.md`, `docs/proof-S4.md`, `docs/proof-S42.md`, `docs/proof-S43.md` | refereed proof routes |
| `docs/decisions/` | dated decision records |
| `docs/lessons.md` | lessons, each with a rule and (where possible) a check |
| `docs/calibration.md` | referee calibration rounds (planted errors, sealed keys) |
| `docs/progress.md` | chronological log |
| `CHANGELOG.md` | released versions |
| `docs/toolchain.md`, `docs/dependencies.md`, `docs/commitment-format.md` | toolchain, pins, commitment format |
| `docs/prior_art.md`, `docs/upstream.md` | prior-art gate; Mathlib candidates (no PR without the owner) |
| `docs/replay/` | committed `verify-all` and replay records |

Code: Apache-2.0 (`LICENSE`). Documentation: CC BY 4.0 (`LICENSE-docs`). Citation: `CITATION.cff`.
