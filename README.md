# OscInt

[![DOI](https://zenodo.org/badge/1447411529.svg)](https://doi.org/10.5281/zenodo.24021328)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--9478--6061-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0001-9478-6061)

Author: Thomas Falk III ([ORCID 0009-0001-9478-6061](https://orcid.org/0009-0001-9478-6061)). Cite via `CITATION.cff` or the Zenodo record: all versions
[10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328), v0.3.0
[10.5281/zenodo.24045231](https://doi.org/10.5281/zenodo.24045231), v0.2.0
[10.5281/zenodo.24021329](https://doi.org/10.5281/zenodo.24021329).

A Lean 4 + Mathlib library of uniform oscillatory-integral estimates in one and two variables: van der Corput with
explicit constants (S1), nondegenerate stationary phase uniform in a linear term (S2), the uniform fold
estimate m^{-5/6} (S3), and the uniform D4 estimate t^{-2/3} (S4.1, S4.1′), the limit t^{2/3}∫e^{itφ}A → c_C A(0) with a Gamma-free c_C (S4.2), c_C > 0 (S4.3) and the
closed form of c_C (S4.4), Mathlib-idiom front ends and conversions (F1, F2, C1–C9, C7′, FE-S2.1, FE-S2.2, FE-S3,
FE-S4.1′), compact families and local smoothness (front-end batch 3), and global decay from a pointwise classification
of the phase with the 2D lattice-Laplacian dispersive estimate t^{-2/3} and its sharpness (batch GD; that example is
classical and separable, `docs/prior_art.md`), and explicit constants for the 1D and 2D lattice kernels (batch LE); every statement
with a row in `docs/STATUS.md` has its status there, derived from evidence files. Which theorem to use:
`docs/which-theorem.md`.
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
| S4.4 closed forms of c_C (the brief's Γ(1/3)²/(√3\|Disc\|^{1/6})) | machine-checked as stated (`OscInt.d4ConstantClosedForm`; verify-all PASS). The brief's limit with its constant is S4.2 ∧ S4.4 (`OscInt.d4Limit`, `OscInt.d4ConstantClosedForm`) |
| F1, F2 front end (`ContDiff` amplitudes; the D4 limit with its closed-form constant as one theorem) | machine-checked as stated (`OscInt.API.ampBoundOfContDiff`, `OscInt.API.d4LimitClosedForm`; bridges drafted before the review, disclosed), see `docs/STATUS.md` |
| Front-end batch 2: conversions C1–C9, C7′ (`iteratedFDeriv`, Hessian matrices, `Cubic.discr`, kernel/rank fold condition, norms, `HasCompactSupport`) and front ends FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′ (`OscInt.API.*`, `import OscInt.API`) | see `docs/STATUS.md` (post-proof FAITHFUL ×2; final replay record named there) |
| Front-end batch 3: compact families (S2.2F, S3c, C10), local smoothness (FE-S2.1L/S2.2L/S3L/S4.1′L, single-phase forms) | see `docs/STATUS.md` (one-time waiver of CONTRIBUTING step 5, ratified by the owner 2026-11-09) |
| Batch GD: global decay from a local classification (GD-C, GD, GD-F, GD-N), sharpness (SH), torus unfolding (T1), 2D lattice-Laplacian dispersive estimate t^{-2/3} and its leading term (T6, T6L) | see `docs/STATUS.md`; example `examples/consumer/ConsumerLattice.lean`. T6 and T6L are classical (the kernel factorises into 1D Bessel kernels, `docs/prior_art.md`) |
| Batch VT: GD-C-V, GD-V, GD-F-V, GD-N-V, the global decay estimates for amplitudes in any complex Banach space (matrices, ℂⁿ, bounded sequences), one constant for every E | see `docs/STATUS.md`; example `examples/consumer/ConsumerVector.lean` |
| Batch LE: explicit constants, T0E (1D kernel), T6F (factorisation), T6E (2D, (A+B)² ≈ 4754); content only for t > 518 / t > 1321 | see `docs/STATUS.md`; example `examples/consumer/ConsumerLatticeExplicit.lean` |

"As stated" means the hypotheses in `docs/statements.md` (derivatives continuous up to the endpoints, as in the
source's C^k assumption). Details and evidence: `docs/STATUS.md`.

## Depending on OscInt

Add OscInt to your Lake project and pin a release (Mathlib comes with it, at the revision OscInt was checked with;
use the same `lean-toolchain`, `leanprover/lean4:v4.35.0`):

```toml
# lakefile.toml
[[require]]
name = "oscint"
git = "https://github.com/thomas-falk-research/lean-oscillatory"
rev = "v0.4.0"   # a release tag (pins and notes: docs/release-notes/v0.4.0.md)
```

v0.3.0 is the first release with `OscInt.API`, `stamps/statements.json` and `tools/oscint_check.py` (v0.2.0 has none
of them). Published 2026-11-07 (GitHub release `v0.3.0`, tag on the release commit recorded in
`docs/release-notes/v0.3.0.commit`; CI job `release-pin` checks this, and that `main` contains it). External dry run
with these exact steps: `docs/replay/2026-11-08-external-downstream-dry-run-v0.3.0.txt` (build and checker PASS).
A tested project of this shape: `examples/consumer-release/`.

```bash
lake update oscint
lake exe cache get
lake build
```

Import `OscInt.API` (the entry point: every theorem with the textbook statement it formalises, and front-end
forms in Mathlib's idiom; `tools/check_entry_point.sh` checks that it exposes every name in `stamps/statements.json`).
Use the theorems by their statement names; their types *are* the reviewed statements. For a phase given by a formula,
see `examples/consumer/ConsumerFormula.lean` (front ends FE-S3, FE-S4.1′ with Mathlib-only hypotheses, derivative data
from `OscInt.API.Poly`):

```lean
import OscInt.API

open OscInt.Statements in
example : D4LimitStatement := OscInt.d4Limit

-- the D4 limit with its closed-form constant, for one C² amplitude (no `AmpBound`)
example : OscInt.Statements.D4LimitClosedFormStatement := OscInt.API.d4LimitClosedForm
```

`stamps/statements.json` lists every pinned statement with its label, summary, proving theorem, statement file, the
commitment to its definitional closure and the stamp that froze it, and every statement file with its SHA-256. In
your CI, after `lake build`:

```bash
lake build OscInt Blueprint   # the check replays every OscInt and Blueprint module, not only those you import
python3 .lake/packages/oscint/tools/oscint_check.py \
  --statement OscInt.Statements.D4LimitStatement \
  --expect-sha256 <sha256 of stamps/statements.json, from docs/release-notes/<tag>.md>
```

It checks that your toolchain and Mathlib are the ones OscInt was checked with, that no statement file was edited,
that each statement constant comes from its frozen file, that the proving theorem's type is syntactically the
statement and its axioms are only `propext`, `Classical.choice`, `Quot.sound`, it replays every OscInt module in
Lean's kernel (`leanchecker`), and it recomputes each commitment (about 20 minutes in all; `--fast` skips the last
two and reports PARTIAL, never PASS). Its negative controls are `tools/test_oscint_check.sh`, run in CI on
`examples/consumer/`.

What it does not give you: run from inside the package, the checker and `oscint-commit-env` are the package's own,
so it detects accidental drift (another version, an edited file, a stale build, another Mathlib), not deliberate
tampering. Against tampering, keep your own copy of `tools/oscint_check.py` at a reviewed version (its SHA-256 and
that of `stamps/statements.json` are in the release notes) and pin the release by commit hash. Independent kernels
and the statement reviews are this repository's trust chain (`make verify-all`, "What stays trusted" below).
Versioning, stable names, deprecation and the Mathlib-upgrade rule: `docs/policy.md`.

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
  `OscInt/StationaryPhase/` (S2, S3), `OscInt/D4/` (S4), `OscInt/Front/` (front ends, conversions, hypothesis helpers;
  entry point `OscInt/API.lean`).
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
| `docs/proof-S2S3.md`, `docs/proof-S4.md`, `docs/proof-S42.md`, `docs/proof-S43.md`, `docs/proof-S44.md` | refereed proof routes |
| `docs/policy.md`, `CONTRIBUTING.md` | versions, stable names, deprecation, Mathlib re-freeze rule; adding a statement end to end |
| `docs/decisions/` | dated decision records |
| `docs/lessons.md` | lessons, each with a rule and (where possible) a check |
| `docs/calibration.md` | referee calibration rounds (planted errors, sealed keys) |
| `docs/progress.md` | chronological log |
| `CHANGELOG.md` | released versions |
| `docs/toolchain.md`, `docs/dependencies.md`, `docs/commitment-format.md` | toolchain, pins, commitment format |
| `docs/prior_art.md`, `docs/upstream.md` | prior-art gate; Mathlib candidates (no PR without the owner) |
| `docs/replay/` | committed `verify-all` and replay records |

## How to cite

Cite the software through its concept DOI, which always resolves to the latest version
([10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328)); to cite the exact version you used, take its
version DOI from the [Zenodo record](https://doi.org/10.5281/zenodo.24021328) (v0.3.0:
[10.5281/zenodo.24045231](https://doi.org/10.5281/zenodo.24045231)). GitHub's "Cite this repository" button reads
`CITATION.cff`, and `codemeta.json` carries the same metadata for software indexes.

```bibtex
@software{FalkIII_OscInt,
  author    = {Falk III, Thomas},
  title     = {{OscInt}: uniform oscillatory-integral estimates in {Lean} 4 and {Mathlib}},
  publisher = {Zenodo},
  year      = {2026},
  doi       = {10.5281/zenodo.24021328},
  url       = {https://github.com/thomas-falk-research/lean-oscillatory},
  note      = {ORCID 0009-0001-9478-6061}
}
```
(`@software` is biblatex; with classic BibTeX use `@misc` and the same fields.) If you use the one-dimensional van der
Corput results, please also cite J. Roos and M. Praveen, [`roos-j/lean-oscillatory`](https://github.com/roos-j/lean-oscillatory),
from which they are derived.

## Licence

Code, configuration and data: Apache-2.0 (`LICENSE`). Documentation: CC BY 4.0 (`LICENSE-docs`). Per-file
licensing follows the [REUSE specification 3.3](https://reuse.software/spec-3.3/) (comment headers, `REUSE.toml`,
`LICENSES/`; checked by `reuse lint` in CI). The one-dimensional van der Corput proofs are derived from
`roos-j/lean-oscillatory` (Apache-2.0) and keep its copyright notice. Citation metadata: `CITATION.cff`, `codemeta.json`.
