<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batches SPL-N, A5U and LOC2: answers to the blind pre-proof reviews (2026-11-28, session 17)

Written by the lead. Three referees from fresh contexts, all of the lead's model family, reviewed the six statements
after the freeze: stamp `stamps/20261128T135153Z-9d2a650ee1ec` on 9d2a650, pinned in 6ce20df. The briefs are outside
the tree (privacy rule 19) and identified by SHA-256 in `docs/progress/2026-11-28-session17-log.md`. Their reports are
not reproduced; findings are in the lead's words. Isolation was by instruction (lessons 61): each referee was told
which repository files and which one scratch directory it could read. The tree was not written while any of them ran
(launched 14:02:45Z at 6ce20df; all three had ended by 15:23Z; the lead worked in scratch only).

**Outcome: six FAITHFUL (referee A); no counterexample to any statement (referees B and C); no BLOCKER, no MAJOR. The
statements stand.** No Lean proof of any of the six exists at the time of these answers.

## 1. Referee A (fidelity, all six statements)

Run time 411 s by the task record. HEAD 6ce20df, clean; `git diff --stat 9d2a650 -- <its files>` empty. One Lean probe
file through the session lock (`#print` with explicit numeric types; `crossEnvelope` at 0, 1 and −5; `tsupport`),
a 60-digit series evaluation of κ, and replays of two plant witnesses (A-f, NC-a), all exit 0 with the three axioms.

Verdicts: SPL-NU, SPL-NL, SPL-NK, SPL-NC, A5U, K2-FQ all FAITHFUL. What its probe settled: `-(3:ℝ)/2` is `−3/2`; every
`rpow` has a positive base (in A5U `s^{−1/4}` is reached only for `s > 1`); no natural-number subtraction or
division; `Real.sqrt` only of nonnegative arguments; `ContDiff ℝ 2` is C²; `boxL2` has the `(2π)^{−2}` normalisation;
the derivatives are `fderiv` on the unit vectors and `iteratedFDeriv ℝ 2` on `![(1,0),(1,0)]`, `![(0,1),(0,1)]`;
the challenge files declare exactly the six constants.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| A-1 | MINOR | No detected plant pins LOC2's explicit constant: L-c, L-e, L-f, L-i are NOT DETECTED; disclosed in the plant record but not in the prose. | Accepted. Dated clarification LOC2-a in `docs/statements.md`. An owed plant with a compiled witness for a smaller factor (the sanity agent's cos² bump refutes any factor below about 0.185 on paper) is recorded with the closed plants of the batch, after the proofs. |
| A-2 | MINOR | No plant moves `∃ C` past `∀ α` in A5U, the most natural fidelity error; the moved form would follow from K2-U. | Accepted. The frozen order is right (A read it and checked it with `#print`). Owed plant with the proofs: a compiled derivation of the moved form from K2-U (a true weakening). |
| A-3 | NIT | The three sanity docstrings say the plants are not in the repository; they are under `docs/replay/plants/2026-11-28-{SPLN,A5U,LOC2}/`. | Accepted; as in batch K2 (K2-a), recorded here rather than editing the files at this stage. |
| A-4 | NIT | `a5u_triRate_window` covers one side of each window only. | Noted; `a5u_fixed` covers the window generically. |
| A-5 | NIT | The SPL-N plants inside the 10⁻⁸ window are undetectable without enclosures (disclosed). | Noted. |
| A-6 | NIT | LOC2 item 2: `√13` bounds the square root of a sum that is about 3.23. | Accepted; covered by clarification LOC2-a. |

## 2. Referee B (truth: SPL-N and LOC2)

Run time 866 s. HEAD 6ce20df, clean. Python 3.13.18, mpmath 1.4.1, python-flint 0.9.0 (Arb at 128 bits), numpy 2.5.5,
scipy 1.18.1, as printed by the running process. No Lean.

- **SPL-NU: certified** on `[0, 20]` by Arb bisection with a mean-value enclosure of `|κ|²`: 4051 boxes, certified
  `sup ≤ 0.721973999932`, smallest margin `cap² − upper bound ≥ 9.8·10⁻¹¹` (box `[1.6246875, 1.6247266]`); for
  `τ ≥ 20` an analytic tail with two integrations by parts (identity checked to 10⁻³⁹, not in Arb): `|κ| ≤ 0.627095`.
  Maximum `≈ 0.72197399899801735` at `τ* ≈ 1.6246006179324004`; cap minus maximum `≈ 1.002·10⁻⁹`.
- **SPL-NL: certified**: `|κ(8123/5000)| = 0.721973998997938042721152817773 ± 1.3·10⁻³¹`, margin `≥ 8.998·10⁻⁹`;
  `8123/5000` is within `8·10⁻¹⁴` of the maximiser. At `13/8` the value `0.72197396587` is below the lower rational.
- **SPL-NK, SPL-NC**: no counterexample; both follow on paper from SPL-I and SPL-A with NU and NL; degenerate cases
  (discontinuous `g₃`, `‖g₃‖₁ = 0`, extreme λ) do not break them; numerical identity checks on six amplitudes.
- **K2-FQ**: no counterexample on adversarial separable C² cutoffs and phases; worst ratio of the localised integral to
  the bound 0.208; `Σ_{ℤ²} (1 + |n|²)^{−2} = 3.22658`.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| B-1 | MINOR | The cap has only about 10⁻⁹ of slack: a proof needs enclosures of κ near `τ ≈ 1.6246` far below 10⁻⁹; crude cells will not close. | Accepted as a constraint on the route, not on the statement. The route's 40-cell certificate has minimum squared slack `9.09·10⁻¹⁰` and survives a fourfold Taylor remainder (session log, lead's check). |
| B-2 | NIT | SPL-NC's proof through SPL-A needs `‖g₃‖₁ > 0` for the nonzero smooth compactly supported amplitude, which SPL-A does not state. | Accepted; it is a step of the route (SPL-A's `g` is C^∞, so `g₃` is continuous; `g₃ ≡ 0` forces a compactly supported polynomial, hence 0). |
| B-3 | NIT | Naive evaluation of κ at large τ cancels catastrophically. | Noted for numerics; the route uses the asymptotic form for `τ ≥ 4`. |

Its certified enclosures are independent of the packet's code and certificate (ball arithmetic of its own design).

## 3. Referee C (truth: A5U)

Run time 4810 s. HEAD 6ce20df, clean. Python 3.13.18, numpy 2.5.5, scipy 1.18.1, sympy 1.14.0, mpmath 1.3.0; each job
capped at about 4 GB, the longest about 26 minutes. No Lean.

- Paper sketch: an exact reduction `triKernel α t n = 4π i^U ∫₀^π J_U(2t cos s) e^{i(tα cos 2s + S s)} ds` (`S, U` the
  sum and difference of the site coordinates); the reduced function is even in the longitudinal variable; at the A5
  point its sixth coefficient matches TRI-W and its quartic coefficient on the fold curve matches TRI-Q; the family is
  a versal even unfolding (Jacobian determinant −1); only A3 points are born at the bifurcation (no A4 point, no
  swallowtail); a one-variable van der Corput sketch reproduces `C min(t^{−2/3}, ε^{−1/4} t^{−3/4})`.
- Numerics: `sup_n |K| / (t^{−2/3} E(ε t^{1/3}))` stays in `[9.8, 23.1]` for `ε ∈ {0, ±0.05, ±0.1, ±0.14, ±0.2, ±0.3}`
  and `t` up to 2400 (exact DFT, aliasing controlled, cross-checked with a triple Bessel sum to `3.4·10⁻¹⁴`), and up to
  `t = 16000` for `ε ∈ {0, ±0.02, ±0.05}` (exact one-dimensional Bessel formula), bounded on both sides of `a₀` and
  across the crossover `t ≈ ε^{−3}`. This reaches the envelope's second branch, which the registered test did not.
- Verdict TRUE-AS-FAR-AS-TESTED; no formal defect.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| C-1 | info | The window radius must be below `a* ≈ 0.354` (K2-D at α = 0); a large radius inflates C (ratio about 18.8 at `ε = −0.3`). | Consistent with the prose (item 2) and with the sanity theorem `a5u_window_lt`. |
| C-2 | info | For `ε ≥ 0.1`, `t^{3/4} sup` still decreases slowly at `t = 2400` (approach to K2-D's floor). | Noted; does not affect A5U. |

## 4. What follows

No statement is changed. Clarification LOC2-a is added to `docs/statements.md`. The owed plants of A-1 and A-2 are
recorded with the batch's closed plants after the proofs. These answers are stamped before any route referee or proof
agent is launched (lessons 29).
