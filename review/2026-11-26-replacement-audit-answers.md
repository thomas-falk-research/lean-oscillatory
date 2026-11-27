<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# The "replacement research audit" of 2026-11-26: what was checked, and what follows

Written by the lead. The owner delivered an archive from an independent reviewer: a report `AUDIT.md`
(335 lines) and three scripts with their outputs, pinned to 74c4552. The report and scripts are not committed
and not reproduced; every finding below is in the lead's words. The report's claims were treated as claims
until checked.

**Handling.** Archive copied to the lead's scratch and extracted into its own directory; its own checksum list
(nine files) verifies. The three scripts were read before they were run, then run with `python3 -I` from a
different directory. Archive SHA-256 of `AUDIT.md`: 1b02636c9ad9a2e184bd00a25eacbd912ef1a64512eac125fc3bf3bd507b6871.

**Who checked.** The lead only (Claude, Anthropic), not a fresh-context checker; the reviewer is of another model
family (the report's links carry a ChatGPT referral tag). No Lean was run. Nothing below is machine-checked.

**The reviewer did not have reports A to F** (the report says so). Two of its three results duplicate what this
repository already holds; see 2 and 3.

## 1. SPL-N: an enclosure of the optimal constant `C* = sup |κ|`

- Claim: `72197399/10^8 < C* ≤ 360987/500000 (= 0.72197400)`, by exact rational arithmetic on 40 cells of
  `[1/2, 4]` (41 points, 40 Taylor terms each), conditional on analytic facts that the SPL route already states
  (`|κ| ≤ τ`, `|κ″| ≤ 2/τ`, `|κ − L/2| ≤ 4/τ³`, the Fresnel value).
- **Reproduced:** both JSON results of `check_spl.py`, identical. **Independently checked:** `sup |κ| =
  0.72197399899801734661` at `τ = 1.6246006179324` (mpmath 1.3.0, 40 digits, from the Fresnel functions and not
  the script's series; one local maximum above 0.70 on (0, 10)). The enclosure holds, with a margin of about
  1.0e-9 at the top. The lead read the certificate logic: the Taylor remainder, the square-root error (counted
  conservatively), the interpolation bound for a vector-valued C² function and the two end regions are correct.
- **Not new to this repository.** `docs/proof-SPL.md` section 5 already records `max |κ| = 0.7219740` at
  `τ = 1.62460`, and certificates for 73/100 and 3/4 are committed
  (`numerics/results-spl-n-certificates-from-checker-2026-11-20.txt`). The report's "17.5 % smaller" is measured
  against 7/8. Against the planned 73/100 the gain is 1.1 %.
- What is new and useful: a certificate for a bound within 1e-8 of the optimum, at about the cost that section 5
  estimated for 73/100 (about 40 points). The open question is the Lean cost: rationals with powers up to `τ⁸³` in
  a proof-producing arithmetic. That has to be measured before the rational for SPL-N is chosen. Section 5's
  decision (prototype first) stands.

## 2. The third-derivative constant

- Lower witness `4.7965 < ∫ e^{i(x³/6 − 0.777x)} dx < 4.7966` on `[−2.828, 2.828]`: reproduced. It is the
  value already recomputed in ball arithmetic by the checker of report D, and it is Rogers's numerical value
  (`review/2026-11-20-external-reports-answers.md`, section 1).
- Upper bound `C₃ ≤ 2r + 7/√r = 3 + 7√(2/3) ≈ 8.715` (r = 3/2), from VC2-K by splitting where `|f″|` is small:
  correct as hand mathematics (re-derived by the lead), and the classical splitting argument. **It is weaker than
  report D's checked 38/5 = 7.6.** It adds nothing to D.

## 3. The D4-to-cusp transition of `cos x + cos y + α cos(x + y)` (the report's strongest proposal)

- Re-derived by the lead: at `(π/2, π/2)` the gradient is `(−1, −1)`, the Hessian is `α[[1,1],[1,1]]`, and the
  cubic is `(δx³ + δy³)/6`. In `s, v` this is `2αs² + sv² + s³/3`. `Φ(0, v) = 0` exactly, and the reduced
  quartic is `−v⁴/(8α)`. So the point is D4 at α = 0 and A3 for α ≠ 0. The scaling `a = α t^{1/3}` and the
  limiting phase `(X³ + Y³)/6 + (a/2)(X + Y)²` are correct. The quadratic `(X + Y)² ≡ 2XY` modulo the Jacobian
  ideal `(X², Y²)`, so α together with the two linear terms is a versal unfolding of D4. In the polynomial model,
  the only A3 point of the slice `a ≠ 0` is the origin (the third derivative along the kernel vanishes only
  there), which is consistent with the proposed `(1 + |a|)^{−1/4}` envelope.
- The Jacobi–Anger series for `K_α` was re-derived. The script's output is reproduced exactly (40 rows, difference
  0), including the grid cross-check at t = 32 (≤ 1.3e-16). At a = 0 the value 0.200083 agrees with `J_t(t)² ≈
  0.2001 t^{−2/3}`. This is floating point and exploratory, as the report says.
- **Prior art the report does not name:** Duistermaat 1974 (uniform estimates for oscillatory integrals with
  phases in versal unfoldings), as well as Karpushkin and Varchenko, which it does name. The lead recalls
  Duistermaat's paper and has not read it in this session. The exponent statement is very likely
  classical in that framework. The candidate contribution is the explicit, α-uniform lattice statement with
  constants, together with the global (all `n`) part. That has to pass the prior-art gate before it is called
  new.
- **Verdict: CANDIDATE.** This is the most interesting item in the report, and it sits on the library's own ground
  (D4U, A3, the CENSUS). The local scaled-limit theorem (the report's R3/R4 local part) is a reasonable next batch
  after its prior-art gate. The global conjecture stays a conjecture, with the falsification programme the
  report describes.

## 4. The frontier citations

Checked by web search on 2026-11-26 (`docs/progress` is not updated for this; no source is in the bibliography):

- Local smoothing (OpenAI, October 2026) and Wang's exposition arXiv:2611.30274: the paper exists. The lead read
  the statement of the critical annular estimate (`[log(2+R)]^{2/p_c}`), the lower bound `(log R)^{1/p_c}`, and
  the sentence saying the example "does not decide whether the second one" is needed. **The open gap the report
  names is real, as stated.**
- Cheng, arXiv:2609.37300 (discrete fourth-order Schrödinger, `|t|^{−d/4}`): exists, as described.
- Anthropic's black-hole announcement (17 November) and the modular-bootstrap preprint: they exist. The
  repository already uses its Lemma E.1 (batch TSD).
- The Riemann hypothesis (Alpöge, Lean development released 20 November; Lean FRO / Mathlib Initiative statement
  of 21 November; independent rebuild by Sutherland): many secondary reports agree on this. The lead did not read
  the primary Lean community statement in this session. Nothing in this repository depends on it, and the
  report says correctly that it does not change any explicit constant.
- A Tao post of 20 November on unforced Euler and Navier–Stokes: **not found** by the lead's search. Unverified.

## 5. The "research protection" section

Its rules are the rules this repository already follows: frozen statements are never weakened, negative results
are kept append-only, and a claim of impossibility needs a counterexample. The report itself finds no
evidence of interference and says so. One point of fact for the record: the assessment of 2026-11-20 ("none of
the four checked reports answers a question that the literature leaves visibly open") was a finding about those
four reports, with its evidence in section 5 of the answers of that date. It was not a limit on what may be
attempted, and this audit, which says of its own results "not a claim of new mathematics", agrees with it.

## 6. Ranking, with the earlier candidates

1. **D (38/5), unchanged first** for a frozen statement: proved on paper, checked, and cheap. Its prior-art gate
   is still open.
2. **The D4-to-cusp local theorem (this report, section 3).** It is the best route to a result that is not only a
   formalization: an explicit, parameter-uniform estimate across a singular transition. Prior-art gate first
   (Duistermaat, Karpushkin, Varchenko, Ikromov–Müller, Ge et al. arXiv:2412.02947).
3. **SPL-N with the report's rational, if the Lean cost allows it,** otherwise 73/100. Small, and on an
   existing statement.
4. The second logarithm in local smoothing (F1): a real open question, but far from what this library proves
   today. The report's two first steps (a dependency map of the published proof, and a numerical focusing
   experiment that can only refute) are proportionate. A claim of removing the logarithm cannot come from a
   numerical fit.

**The strongest case against this report's value.** Its two executed "results" are already in this repository
in substance (the SPL supremum to seven digits, and the cubic witness) or are dominated (8.715 against 38/5).
Its headline figure is measured against a constant the repository had already planned to replace. What it adds
that is genuinely new here is one well-posed research direction (section 3), one confirmed open problem
(section 4), and a tighter certificate.
