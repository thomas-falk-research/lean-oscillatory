# OscInt

[![DOI](https://zenodo.org/badge/1447411529.svg)](https://doi.org/10.5281/zenodo.24021328)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--9478--6061-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0001-9478-6061)

Author: Thomas Falk III ([ORCID 0009-0001-9478-6061](https://orcid.org/0009-0001-9478-6061)). Cite via `CITATION.cff` or the Zenodo record: all versions
[10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328), v0.4.0
[10.5281/zenodo.24088811](https://doi.org/10.5281/zenodo.24088811), v0.3.0
[10.5281/zenodo.24045231](https://doi.org/10.5281/zenodo.24045231), v0.2.0
[10.5281/zenodo.24021329](https://doi.org/10.5281/zenodo.24021329).

**Machine-checked uniform estimates for oscillatory integrals, in Lean 4 and Mathlib.** OscInt formalises the
estimates that dispersive PDE, semiclassical analysis and lattice dynamics rest on:
- the van der Corput lemma for every derivative order, with explicit constants;
- non-stationary and nondegenerate stationary phase;
- uniform decay at degenerate critical points: the fold (A2, m^{−5/6}), the cusp (A3, t^{−3/4}) and the umbilics
  (D4, t^{−2/3}, with the exact leading term and its Γ(1/3) constant);
- global decay assembled from a pointwise classification of the phase, also for vector-valued amplitudes;
- explicit bounds for the propagator kernel of the free discrete (lattice) Schrödinger equation: on ℤ,
  |∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 8(1 + √7)/3 · t^{−1/3} for all t > 0 and real ξ (for integer ξ the kernel is
  2π i^ξ J_ξ(t), a Bessel function), and on ℤ^d the kernel is bounded by (8(1 + √7)/3)^d t^{−d/3}.

The bounds at degenerate points and the global bounds are uniform over all linear terms of the phase, which is what
dispersive estimates need; stationary phase and the fold bound are uniform over compact sets of linear terms. Statements are
written, timestamped and reviewed blind before their proofs (the few exceptions are disclosed in `docs/STATUS.md`),
and every proof is replayed by six kernel checkers: Lean's own kernel in two modes and four independent
implementations. A downstream project can check in CI that it depends on exactly the reviewed statements.

- **63 pinned statements; 59 are machine-checked as stated.** The other four, batch LS (the free lattice Schrödinger
  group on ℓ²(ℤ^d)), are stated, frozen and reviewed, with a refereed proof route, and are not yet proved.
- **Entry point:** `import OscInt.API`. Which theorem to use: `docs/which-theorem.md`. Recipes: `docs/cookbook.md`.
  Machine-readable index: `docs/api.json`.
- Lean package `OscInt`; toolchain v4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag v4.35.0).
- Proofs and reviews are largely by AI agents (Claude instances, as the commit trailers record). Work drafted with
  an external reviewer's tools names those tools in `docs/prior_art.md`. Statement fidelity has been read by AI
  referees only, not yet by a human expert.

## What is proved

"Machine-checked as stated" means every row of the trust chain (below) exists for that statement, with the
hypotheses in `docs/statements.md`, for example derivatives continuous up to the endpoints, as in the source's C^k
assumption. The status of each statement, with its evidence: `docs/STATUS.md`.

| Statements | Lean names | Status |
|---|---|---|
| **One variable.** S1: van der Corput for k = 1, 2, 3 (constants 3, 8, 18). S1.k: every k ≥ 2, constant 5·2^{k−1} − 2, uniform in a linear term | `OscInt.vanDerCorput_one/two/three`, `OscInt.API.vdCk` | machine-checked as stated; S1.k AI-assisted, disclosed. S1 is ported from roos-j/lean-oscillatory (Roos–Praveen, Mathlib PR #39406), which also anticipates S1.k (`docs/prior_art.md`) |
| **Two variables, local.** S2.1 non-stationary phase; S2.2 nondegenerate stationary phase; S3 the fold, m^{−5/6} | `OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold` | machine-checked as stated (S3: fold condition on all of K) |
| **Cusp (A3), local.** S5.1 stable cusp and S5.1′ any A3 point: t^{−3/4} for C² amplitudes supported in a small ball around the point, uniform in the linear term | `OscInt.API.cuspBound`, `OscInt.API.cuspBoundGen` | machine-checked as stated (2026-11-13); AI-assisted proof, disclosed |
| **Umbilics (D4).** S4.1, S4.1′ the uniform bound t^{−2/3}; S4.2 the limit t^{2/3}∫e^{itφ}A → c_C A(0); S4.3 c_C > 0 with a Gamma-free proof; S4.4 the closed forms Γ(1/3)²/(√3\|Disc\|^{1/6}) and Γ(1/3)²/Disc^{1/6} | `OscInt.d4Bound`, `d4BoundNe`, `d4Limit`, `d4ConstantPos`, `d4ConstantClosedForm` | machine-checked as stated |
| **Front ends in Mathlib's idiom.** F1, F2; conversions C1–C10, C7′ (`iteratedFDeriv`, Hessian matrices, `Cubic.discr`, kernel and rank forms of the fold condition, norms, `HasCompactSupport`); FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′; compact families S2.2F, S3c; local smoothness (…L forms) | `OscInt.API.*` | machine-checked as stated (front-end batch 3 under a one-time waiver, ratified by the owner 2026-11-09) |
| **Global decay** from a pointwise classification (GD-C, GD, GD-F, GD-N), also for amplitudes in any complex Banach space (GD-…-V); sharpness (SH); torus unfolding (T1) | `OscInt.API.globalDecay`, … | machine-checked as stated |
| **Lattice kernels.** T6, T6L: the 2D lattice Laplacian decays like t^{−2/3}, sharply (classical and separable). T0E, T6F, T6E: explicit but weak constants (content only for t > 518 and t > 1321). T0E′, T6E′: the cube-root constant 8(1 + √7)/3, within a factor 2 of the best, useful from t ≈ 3.70 (AI-assisted, disclosed). TdF, TdE′: the d-dimensional hypercubic kernel factorises and is bounded by (8(1 + √7)/3)^d t^{−d/3} | `OscInt.API.latticeLaplacianDecay`, `latticeKernel1CubeRoot`, `latticeLaplacianCubeRoot`, `hypercubicKernelFactor`, `hypercubicCubeRoot`, … | machine-checked as stated. The rates are classical (Stefanov–Kevrekidis 2005); the constants are new only through T0E′ (`docs/prior_art.md`) |
| **Batch LS.** LS-E, LS-K, LS-D, LS-D′: existence of the free lattice Schrödinger group on ℓ²(ℤ^d), its kernel representation, uniqueness, and dispersive decay with explicit constants | `OscInt/Statements/LatticeGroup.lean` | **stated, frozen and reviewed; not proved.** Route `docs/proof-LS.md`, with a compiled assembly |

Worked examples, which also check that the hypotheses can be met (`examples/consumer/`): the lattice Schrödinger
kernel, single photons on a cosine-band lattice, cold-plasma waves, phase mixing, whistler waves, matrix-valued
amplitudes, and phases given by formulas. Where the results apply: `docs/applications.md`.

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

v0.5.0 is prepared (`docs/release-notes/v0.5.0.md`) and is published by the owner; until its tag exists, pin v0.4.0.

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
  `OscInt/StationaryPhase/` (S2, S3), `OscInt/D4/` (S4), `OscInt/Cusp/` (S1.k, S5.1, S5.1′), `OscInt/Front/` (front
  ends, conversions, hypothesis helpers, global decay, lattice kernels; entry point `OscInt/API.lean`).
- `Blueprint/` intermediate propositions (definitions only); `Challenge/` `sorry` theorems over the statement modules
  for `lake comparator` (never imported; frozen by the stamped export hash and the pinned statement-file hashes,
  `stamps/pins.txt`); one `comparator*.json` per milestone.
- Checks run by `make lean`: `Axioms.lean` (axiom audit), `StatementTypes.lean` (final types are the frozen
  constants), `MathlibNames.lean` (names the plan relies on), `GammaFree.lean` (S4.3 proof method).
- `tools/` Rust binaries (std only) and the Lean commitment producer; `numerics/` floating-point probes (tooling,
  never evidence); `stamps/` timestamp records; `review/` the lead's answers to every review (`review/README.md`; older verbatim
  reports are in history only, owner privacy rule).

## Documents

| File | Content |
|---|---|
| `docs/README.md` | index of all documents, with the statement labels |
| `docs/which-theorem.md`, `docs/cookbook.md`, `docs/api.json` | which theorem to use; copy-paste recipes; machine-readable API index |
| `docs/applications.md` | where the results apply (models and domains), with worked examples |
| `docs/statements.md` | the mathematics of every statement, with dated clarifications |
| `docs/STATUS.md` | evidence-derived status per statement |
| `docs/HANDOFF.md` | state and next steps for the next session |
| `docs/ROADMAP.md` | the path to a production-ready library, as a checklist |
| `docs/proof-*.md` | refereed proof routes, one per batch (S2S3, S4, S42, S43, S44, API2, API3, GD, VT, LE, LE2, HC, A3, LS) |
| `docs/policy.md`, `CONTRIBUTING.md` | versions, stable names, deprecation, Mathlib re-freeze rule; adding a statement end to end |
| `docs/decisions/` | dated decision records |
| `docs/lessons.md` | lessons, each with a rule and (where possible) a check |
| `docs/calibration.md` | referee calibration rounds (planted errors, sealed keys) |
| `docs/progress.md` | chronological log of sessions 1–3; sessions 7–10 are in `docs/HANDOFF.md`, sessions 4–6 in its history and in `CHANGELOG.md` |
| `CHANGELOG.md`, `docs/release-notes/` | released versions; per-release pins of the trust chain |
| `docs/toolchain.md`, `docs/dependencies.md`, `docs/commitment-format.md` | toolchain, pins, commitment format |
| `docs/prior_art.md`, `docs/upstream.md` | prior-art gate; Mathlib candidates (no PR without the owner) |
| `docs/replay/` | committed `verify-all` and replay records |

## How to cite

Cite the software through its concept DOI, which always resolves to the latest version
([10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328)); to cite the exact version you used, take its
version DOI from the [Zenodo record](https://doi.org/10.5281/zenodo.24021328) (v0.4.0:
[10.5281/zenodo.24088811](https://doi.org/10.5281/zenodo.24088811); v0.3.0:
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
