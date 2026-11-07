<!-- Blind statement review of front-end batch 1 (F1, F2), referee B (fresh-context agent, prompt review/prompts/API1-pre-proof.md), commit eb8e621. Verbatim final report. -->

eb8e6214e96dcf4ca24cfad2cff15f12ed962336
(Read from `.git/HEAD` → `.git/refs/heads/claude/tender-ride-nfyppc`, since I was told not to run git. Nothing in the repository was modified. Scratch files are in /tmp/apiB/ only.)

# Referee B report: F1 `AmpBoundOfContDiffStatement` and F2 `D4LimitClosedFormStatement`

Files read: `docs/statements.md` (S2/S3, S4, "Front end, batch 1"), `OscInt/Statements/FrontEnd.lean`, `D4Limit.lean`, `D4.lean`, `StationaryPhase.lean`.

**Bottom line:** both statements are faithful and true. There are no BLOCKER or MAJOR findings, only MINOR and NIT items, all about the sanity theorems and docs.

## 1. Verdicts

**F1: FAITHFUL to the docs, and TRUE.**
- The Lean text says exactly what F1 in the docs says: `∀ n K A, IsCompact K → ContDiff ℝ n A → tsupport A ⊆ K → ∃ M, AmpBound n K A M`.
- I proved it with no sorry in /tmp/apiB/Check.lean (about 10 lines):
  - `HasCompactSupport.intro hK …` gives compact support.
  - For each j ≤ n, `continuous_iteratedFDeriv` plus `bddAbove_range_of_hasCompactSupport (hcs.iteratedFDeriv j)` gives a bound.
  - Take M = Σ_{j<n+1} max(B j, 0).
- It is not trivially true or false for any n. Edge cases:
  - **n = 0:** `ContDiff ℝ 0` means continuous, and ‖iteratedFDeriv ℝ 0 A k‖ = ‖A k‖. Fine.
  - **Orders above n:** never constrained (`j ≤ n`).
  - **K = ∅:** forces A = 0, so M = 0 works.
  - **Non-compact K:** excluded by the hypothesis.

**F2: FAITHFUL to the docs' F2. TRUE, given the frozen S4.2 and S4.4.**
- Against the brief's S4 it is FAITHFUL-STRONGER. On Disc < 0 it states exactly the brief's limit, t^{2/3}∫e^{itφ}A → Γ(1/3)²/(√3|Disc C|^{1/6})·A(0). It adds the elliptic branch Disc > 0, and it allows C² amplitudes rather than smooth ones.
- **Checking `d4ClosedConstant` against c_C = I·J(C)/3 (I = Γ(2/3)/2).** Script /tmp/apiB/c.py, mpmath at 30 digits, J by quadrature split at the zeros of C(cos θ, sin θ):

| (a, b, c, d) | Disc | I·J/3 | closed form | rel. diff |
|---|---|---|---|---|
| (1, 0, 0, 1) | −27 | 2.39223722423 | 2.39223722425 | 8e-12 |
| (1, 0, −3, 0) | 108 | 3.28867941090 | 3.28867941090 | 4e-14 |
| (1, 2, 3, 5) | −367 | 1.54853322249 | 1.54853322252 | 2e-11 |
| (0, 1, 1, 0) | 1 | 7.17671167255 | 7.17671167274 | 3e-11 |
| (2, −7, −3, 1) | 2677 | 1.92597555257 | 1.92597555259 | 8e-12 |
| (1.5, −2, 0.7, −0.3) | −3.8255 | 3.31321920613 | 3.31321920612 | 4e-12 |
| (−1, 4, 1, −2) | 568 | 2.49383343163 | 2.49383343166 | 1e-11 |

  - Three of these cubics have all four coefficients nonzero: one hyperbolic, (1, 2, 3, 5), and two elliptic, (2, −7, −3, 1) and (−1, 4, 1, −2).
  - The differences are at the level of quadrature error near the singular points.
- **Two hand checks that do not use the polar formula:**
  - x³ + y³: (∫_ℝ e^{ix³}dx)² = (Γ(1/3)/√3)² = Γ(1/3)²/3, which matches √3·27^{1/6} = 3.
  - x³ − 3xy²: J = 2B(1/2, 1/6), so c = √π Γ(1/6)/3 = Γ(1/3)²/(2^{1/3}√3) = Γ(1/3)²/108^{1/6}. This uses Legendre's formula for Γ(1/6).
  - Together with the covariance c(C∘L) = c(C)/|det L| and Disc(C∘L) = det(L)⁶·Disc(C), these confirm both branches.
- The sign conventions are right. Disc < 0 means one real linear factor (hyperbolic umbilic D4⁺); Disc > 0 means three (elliptic umbilic D4⁻). The convention a = ∂₁₁₁/6, b = ∂₁₁₂/2, and so on matches C = (1/6)D³φ(0)[κ³].

## 2. Does F2 follow from S4.2, S4.4 and F1? Yes, and it is strictly a front end.

I proved `D4LimitStatement → D4ConstantClosedFormStatement → AmpBoundOfContDiffStatement → D4LimitClosedFormStatement` in /tmp/apiB/Check.lean. It compiles with no errors and no sorry.
- **Proof:** take δ from S4.2 and M from F1 (applied with `isCompact_closedBall 0 δ`), then `rw` the constant using `h4.2.1` or `h4.2.2` after splitting the `if`.
- **Integral:** the written-out integral is syntactically `oscInt2 (fun κ => t * φ κ) A` up to beta reduction. `exact` closed it with no conversion.
- **Quantifier order:** `∃ δ > 0, ∀ A` is the same as in S4.2. δ depends only on φ.
- **Coercions:** `((t ^ ((2:ℝ)/3) : ℝ) : ℂ)` is `Real.rpow` cast to ℂ, identical to S4.2; only t → ∞ matters. The constant is cast ℝ → ℂ.
- **`tsupport` versus support:** `tsupport` is the same as in `AmpBound`. Because `closedBall` is closed, `tsupport A ⊆ closedBall 0 δ` is equivalent to `support A ⊆ closedBall 0 δ`, so there is no difference.
- **Max-norm ball:** `closedBall 0 δ` on ℝ × ℝ is the square [−δ, δ]². δ is existential and the square and Euclidean balls nest, so this is harmless.
- **Nothing stronger slipped in.** Conversely, F2 together with S4.4 gives back S4.2, because `AmpBound` implies the F2 hypotheses on A. So F2 is equivalent to S4.2 once the constant is rewritten.

## 3. Vacuity and conventions

- **`d4ClosedConstant` at D = 0:** it takes the `else` branch, and `Real.zero_rpow` gives 0^{1/6} = 0, so the value is Γ²/0 = 0. I checked `d4ClosedConstant 0 = 0` by `simp`. This junk value is never reached, because F2 assumes `disc ≠ 0` and S4.4 needs a sign.
- **The `if`:** `D < 0` selects the brief's branch correctly. In the else branch with D > 0, `D ^ (1/6)` is positive rpow. `|D| ^ (1/6)` is applied only to |D| > 0. There is no rpow of a negative base anywhere.
- **`Real.Gamma (1 / 3)`:** the argument is the real 1/3, as intended.
- **F2 is non-vacuous:** its phase hypotheses are satisfiable (`sanity_D4Limit_hyps`, x³ + y³). For every δ there is a C² bump A with A(0) = 1 and support in the δ-ball. The constant is positive (`sanity_d4ClosedConstant_pos`), so the conclusion has bite.

## 4. Sanity theorems in `FrontEnd.lean`

- **`sanity_AmpBoundOfContDiff_hyps`:** shows the F1 hypotheses are satisfiable by a nonzero amplitude, but only for n = 2 and K = closedBall 0 2. It says nothing about the conclusion (`sanity_ampBound_exists` in `StationaryPhase.lean` covers that). It also does not exercise an arbitrary δ for F2, though bumps of any radius obviously exist.
- **`sanity_d4ClosedConstant_cubes`:** a real test. It ties the D < 0 branch to an independent textbook value, Γ(1/3)²/3 for x³ + y³. Combined with `sanity_D4_hyps` (disc = −27) it would catch a √3 or |D| slip on that branch.
- **`sanity_d4ClosedConstant_pos`:** a genuine bite test; it rules out the junk value 0 for D ≠ 0.
- **`sanity_d4ClosedConstant_branches`:** only unfolds the definition at −367 and 1. It would catch the two branches being swapped, or |D| being swapped with D. But it restates the definition, so it cannot catch a wrong formula: for example Γ(1/3)²/D^{1/6} missing a factor on the elliptic branch would pass.
- **What the sanity theorems miss:**
  - There is no independent value for the elliptic branch.
  - No phase with disc > 0 is shown to satisfy the F2 hypotheses; `sanity_D4Limit_hyps` covers only disc = −27.
  - There is nothing connecting `disc (cubicCoeffs φ)` to a cubic with all coefficients nonzero.
  - None of this is load-bearing for truth, which I checked numerically and analytically above.

## 5. Findings

No BLOCKER. No MAJOR.

- **MINOR 1: the elliptic branch has no independent sanity value.** `sanity_d4ClosedConstant_branches` (`d4ClosedConstant 1 = Real.Gamma (1 / 3) ^ 2`) restates the definition. Suggestion: add a sanity for x³ − 3xy², (1, 0, −3, 0), disc 108. Its value is Γ(1/3)²/108^{1/6} = Γ(1/3)²/(2^{1/3}√3) ≈ 3.2886794109, which equals √πΓ(1/6)/3 independently. The Lean form could state disc = 108 and the rpow simplification, as was done for −27.
- **MINOR 2: no sanity shows the F2 hypotheses for a disc > 0 phase.** For example, φ = x³ − 3xy² gives `disc (cubicCoeffs φ) = 108`. Only x³ + y³ (disc < 0) is covered.
- **NIT 3: the `d4ClosedConstant` docstring does not mention the D = 0 value.** It says "`Γ(1/3)²/D^{1/6}` otherwise (used for `D > 0` …)" but not that the value at D = 0 is the junk 0. The docs say only "never used". A one-line note would help.
- **NIT 4: `sanity_AmpBoundOfContDiff_hyps` is fixed to n = 2 and radius 2.** Its docstring claims satisfiability of "F1's hypotheses", which are quantified over n and K.
- **Process note, not a defect:** the bridge was drafted before review, as disclosed. My own bridge, written independently, confirms F2 follows from S4.2 ∧ S4.4 ∧ F1 by a short argument with no hidden strengthening.

## Scratch files (all in /tmp/apiB/)

- /tmp/apiB/Check.lean: the F2 implication, the F1 proof, and `d4ClosedConstant 0 = 0`. Compiled with `nice -n 10 lake env lean`, no output.
- /tmp/apiB/c.py: the numerical check of the closed form against I·J/3.
