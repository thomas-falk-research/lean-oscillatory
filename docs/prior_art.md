# Prior art (gate run 2026-11-05)

Searched by a fresh-context search agent (sources it read are marked A) and spot-checked by the lead (L: file
downloaded and read in this session). Nothing listed was built by us. "Not found" means PLAUSIBLE-not-novel: the
search can miss work, notably Lean Zulip threads (the archive was not searchable from this session) and private
repositories.

## Verdicts

| Target | Verdict | Basis |
|---|---|---|
| S1 1D van der Corput, constants 3, 8, 18, amplitude | **ANTICIPATED** (not merged in Mathlib) | roos-j/lean-oscillatory, Mathlib PR #39406 |
| S2 2D nondegenerate stationary phase, uniform in p | PARTIAL | non-stationary O(μ^{-N}) in ℝⁿ and O(λ^{-n/2}) for *definite* Hessians, existential constants (roos-j/lean-variationalsw); no indefinite case |
| S3 uniform fold, m^{-5/6} | not found | only a 1D cubic-point limit (lean-DLMF) |
| S4 D4 umbilic, t^{-2/3}, constant Γ(1/3)²/(√3·\|Disc\|^{1/6}) (and, found here, Γ(1/3)²/Disc^{1/6} for the elliptic umbilic; PLAUSIBLE known, no novelty claimed) | not found | lean-DLMF defines umbilic canonical integrals on complex contours; their link to real integrals is `sorry` there |
| Infrastructure | PARTIAL | Mathlib: whole-space integration by parts, normed-parameter IFT, non-parametric multivariate Taylor (`docs/toolchain.md`) |

## Sources

| Item | URL | What it proves | Verdict | Read |
|---|---|---|---|---|
| roos-j/lean-oscillatory `LeanOscillatory/VanDerCorput.lean` at `cf564e0e100e91de222a53b85b106fa9a03a0ec5` (Joris Roos, Manasa Praveen; Apache-2.0 header; Lean v4.32.0-rc1) | https://github.com/roos-j/lean-oscillatory | `c k = 5·2^(k−1) − 2`. `norm_integral_exp_mul_I_le_of_order_one`: `ContDiffOn ℝ 2 φ [[a,b]]`, `L ≤ \|derivWithin φ\|`, `derivWithin φ` monotone, `0 < L`, `ψ` `ContDiffOn ℝ 1` (Banach-valued) ⇒ `‖∫ exp(φ x·I)•ψ x‖ ≤ c 1·L⁻¹·(‖ψ b‖ + \|∫‖derivWithin ψ‖\|)`. `…_order_ge_two` (k ≥ 2, `ContDiffOn ℝ k φ`, `L ≤ \|iteratedDerivWithin k φ\|`): `c k·L^(−1/k)·(…)`. 494 lines, no `sorry` | ANTICIPATES S1 | L, A |
| Mathlib PR #39406 "van der Corput's lemma" (same authors), open, `awaiting-author` | https://github.com/leanprover-community/mathlib4/pull/39406 | the file above as `Mathlib/Analysis/OscillatoryIntegrals/VanDerCorput.lean` | ANTICIPATES S1 | A |
| roos-j/lean-dfr `DFR/Auto/VanDerCorput.lean` | https://github.com/roos-j/lean-dfr | first derivative 4/μ (no amplitude); k ≥ 2 with existential constant | PARTIAL S1 | A |
| fxeqxmulfx/transformer `Section5_*DerivativeTest` | https://github.com/fxeqxmulfx/transformer | first derivative 4/(\|ρ\|δ), second 10/√(\|ρ\|κ), no amplitude | PARTIAL S1 | A |
| roos-j/lean-spherical `RS/KernelEstimate.lean`, `OneDimStationaryPhase.lean` | https://github.com/roos-j/lean-spherical | second-derivative test with amplitude, (10M + 2M₁(b−a))/√(λκ); 1D quadratic stationary phase | PARTIAL S1, 1D analogue of S2 | A |
| roos-j/lean-variationalsw `OscillatoryIntegralEstimates.lean`, `CarlesonSjolin.lean` | https://github.com/roos-j/lean-variationalsw | ℝⁿ non-stationary phase ≤ C μ^{−N} Σ∫‖D^k a‖; strongly convex phase ≤ C λ^{−n/2}; 2D integration by parts for O(μ^{−4}) | PARTIAL S2, infrastructure | A |
| bjbraams/lean-DLMF `Analysis/Asymptotics/StationaryPhase.lean`, `CoalescingSaddles/*` | https://github.com/bjbraams/lean-DLMF | 1D cubic-point limit λ^{1/3}∫ → Γ(4/3)c^{−1/3}e^{iπ/6}; umbilic canonical integrals (contour definitions), scaling; real-integral representations `sorry` | PARTIAL (adjacent to S3, S4) | A |
| fpvandoorn/carleson `Classical/VanDerCorput.lean`, `HolderVanDerCorput.lean` | https://github.com/fpvandoorn/carleson | linear phase e^{inx} bound; Hölder version on doubling spaces | UNRELATED | A |
| rwst/lean-code, TomasOrtega/Sidon, roos-j/lean-discretesw | (see agent log) | van der Corput *difference inequality* for exponential sums | UNRELATED | A |
| AxiomMath/PrimeNumberTheoremAnd `IEANTN/ZetaAppendix.lean` | https://github.com/AxiomMath/PrimeNumberTheoremAnd | 1D first-derivative non-stationary bound | PARTIAL S1 | A (blueprint text only) |
| Isabelle AFP (mirror) | https://github.com/isabelle-prover/mirror-afp-devel | code search "Corput", "oscillatory", "stationary phase": nothing | not found | A |
| Rocq: MathComp-Analysis, Coquelicot | https://github.com/math-comp/analysis | "Corput", "oscillatory": nothing | not found | A |
| HOL Light, HOL4 | https://github.com/jrh13/hol-light, https://github.com/HOL-Theorem-Prover/HOL | "Corput": nothing | not found | A |
| zbMATH Open API | https://api.zbmath.org/v1/document/_search | "stationary phase & formal proof": 13 hits, all informal | not found | A |
| arXiv API | https://export.arxiv.org/api/query | "van der Corput" ∧ Lean, "stationary phase" ∧ Lean, formalization ∧ oscillatory: nothing relevant | not found | A |
| Mathlib at the pin | local clone | no van der Corput, no stationary phase (`docs/toolchain.md`) | not found | L |

Not checked directly: PFR, sphere-eversion, FLT (their repositories could not be listed from the session; none
appeared in the cross-repository code searches), Lean Zulip archive.

## Consequence

S1 must cite roos-j/lean-oscillatory and PR #39406. Building it again from scratch would duplicate open
upstream work; the decision how to proceed with M1 is the owner's (see `docs/HANDOFF.md`).
