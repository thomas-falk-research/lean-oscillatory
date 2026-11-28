<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Answers to an external review of pull request 26 (batch K2) and to its follow-up on plant F-a (2026-11-28)

The owner delivered two items after the full replay, both from the external party that wrote the K2 research packet
(`review/2026-11-28-K2-packet-answers.md`), both reading the pull request at head 9fa8a27:

1. a review of the pull request (text delivered in the session; not kept in the repository, rule 19);
2. a follow-up document deriving a counterexample to plant F-a (Markdown, SHA-256
   36ab00a7650a9f96e55093d3212089dc426ef87380628dec017624178a7f23fe; kept by the owner). It labels itself a
   derivation on paper with auxiliary exact checks, not compiled in Lean, not human-refereed.

Neither reviewer could run Lean. Each finding is restated in the lead's words and answered. Nobody on the project's
side is a human reader of the mathematics.

## Findings of the review and answers

| # | Finding (lead's words) | Lead's check | Answer |
|---|---|---|---|
| R1 | The six frozen statements meet the batch's mathematical objectives; the packet's routes were integrated substantively. | No action. | Noted. |
| R2 | On a draft pull request the clean-runner jobs of `verify.yml` (build, commitments, replay, comparator matrix, verdict) are skipped, so the draft's CI is not the full evidence. | Confirmed: `.github/workflows/verify.yml` lines 40–41 and 197 skip those jobs for drafts by design. | The pull request is marked ready for review so that they run on the final head; merge only after they pass (owner). |
| R3 | The replay record's "243 lines PASS leanchecker <Module>" counts two whole-export checks as modules. | Confirmed with `grep -c`: 241 module lines plus `leanchecker --from-export` and `leanchecker-paranoid --from-export`. The same miscount is in the TRI record (224 modules, not 226), and it is the miscount session 13 already corrected. | Errata `docs/replay/2026-11-28-K2-verify-all.erratum.txt` and `docs/replay/2026-11-27-TRI-verify-all.erratum.txt`; the records are not edited. The session log and the pull-request description are corrected. |
| R4 | The pull-request description reports two rule-18 deviations; the session log records one. | Confirmed: the log has one rule-18 deviation (02:35, de56a94), one rule-4 deviation (02:15), one intake deviation (the archive extracted before it was listed) and two time corrections (04:01, 04:2x). | Pull-request description corrected. |
| R5 | The push gate should be enforced mechanically, not by the lead's memory. | Agreed; `docs/lessons.md` already says "Check: none automatic (a pre-push hook would be one)" (two entries). | Not done here: it changes `tools/` and the workflow of every session, so it belongs in its own pull request after an owner decision. Recommended. |
| R6 | Plant F-a can be refuted (follow-up document). | Section below. | F-a is false on paper; the compiled outcome stays NOT DETECTED until a witness compiles. |
| R7 | Independent human review is outstanding. | Agreed. | Unchanged in the records. |
| R8 | Merge with a merge commit, never squash or rebase; confirm CI on `main` after the merge. | Consistent with the history of earlier batches. | The owner's step. |

## Plant F-a: the lead's check of the counterexample

The plant (`docs/replay/plants/2026-11-28-K2/plant-F-a.lean.txt`) is `TorusLocalizationStatement` with
`tsupport χ ⊆ (−π, π)²` dropped. Its compiled characterisation `char_F_a` (`witness-F-a.lean.txt`) reduces it at
`χ = 1` to: one `D` such that for every continuous phase `Ψ`, `2π`-periodic in each variable, every real `t`, `p` and
`B`, a bound `B` on all lattice integrals `|∫_{[−π,π]²} e^{i(tΨ + n·k)} dk|` gives `|∫_{[−π,π]²} e^{it(Ψ + p·k)} dk| ≤ D B`.
The document refutes this at `t = 1`, `p = (1/2, 0)`. The lead re-derived each step from the definitions
(`torusBox = Icc (−π, π)²`, `lin p k = p.1 k.1 + p.2 k.2`, Lean's unnormalised integrals) and agrees with each:

1. `f_N(x) = (1/(2N)) Σ_{k≤N} (−1)^k sin kx` has `|f_N| ≤ 1/2` and every Fourier coefficient of modulus at most
   `1/(4N)` (normalised measure `dx/2π`). From `∫ e^{iqx} dx/2π = sin(πq)/(πq)` at `q = k ± 1/2`,
   `∫ sin(kx) e^{ix/2} dx/2π = (−1)^k k / (iπ(k² − 1/4))`, so the signs align and
   `|∫ f_N e^{ix/2} dx/2π| = (1/(2πN)) Σ k/(k² − 1/4) ≥ H_N/(2πN)`.
2. Rudin–Shapiro polynomials (`P_{r+1} = P_r + z^{2^r} Q_r`, `Q_{r+1} = P_r − z^{2^r} Q_r`) have `|P|² + |Q|² = 2M` on the
   circle, `M = 2^r`, so `|P_r| ≤ √(2M)`. The `2M`-cell step function `h` with values `e_0..e_{M−1}, −e_0..−e_{M−1}`
   has mean zero and `|ĥ(l)| ≤ (1/(2M)) |1 − z^M| |P_r(z)| ≤ √(2/M)` for every integer `l` (`z = e^{−iπl/M}`, the cell
   factor is at most `1/(2M)`). With `M ≥ 32N²` this is at most `1/(4N)`.
3. `G_0 = f_N(x) + i √(1 − f_N²) h(y) = e^{i h(y) arccos f_N(x)}` is unimodular; its coefficient at `(k, 0)` is
   `f̂_N(k)` (because `ĥ(0) = 0`) and at `(k, l)`, `l ≠ 0`, it is `i ĝ(k) ĥ(l)` with `|ĝ(k)| ≤ 1`; so all integer
   coefficients are at most `1/(4N)`, while the integral against `e^{ix/2}` equals that of `f_N` (mean of `h` zero).
4. Replacing `h` by a continuous `s` with values in `[−1, 1]` that agrees with `h` off a set of measure at most
   `1/(8N)` gives a continuous biperiodic real phase `Ψ_N = s(y) arccos f_N(x)` (smooth if `s` is) whose exponential is
   within `1/(4N)` of `G_0` in `L¹`. Hence every lattice coefficient is at most `4π²/(2N)` and the fractional integral
   is at least `4π²(H_N/(2πN) − 1/(4N))`, so `D ≥ H_N/π − 1/2 → ∞`.

Notes of the lead (none changes the conclusion):
- The plant asks only `Continuous Ψ`; continuous piecewise-linear ramps at the cell boundaries suffice, so a Lean
  witness needs no mollifier.
- Before smoothing the ratio is exactly `(2/π) Σ_{k≤N} k/(k² − 1/4) ≥ (2/π) H_N`; the document's `H_N/π − 1/2` is a
  conservative bound after smoothing. Both diverge.
- `D` in the plant depends on `χ` only and is chosen before `Ψ`, `t`, `p` and `B`, so a family in `N` refutes it.
  The plant's lattice integrals are `4π² Ĝ(−n)`; the supremum over all `n` is the same.
- Consequence for K2-F: some support condition on `χ` is necessary for the statement, not an artefact of its proof.

Numeric check by the lead (not registered; floating point except criterion A): `numerics/review/k2_fa_check.py`
(SHA-256 99a03894798a5db73b96edf0432a8059207457b53db01b2a3b23264261f7c69f), output
`numerics/results-k2-fa-check-2026-11-28.txt`, OVERALL: PASS, exit 0. It checks the Rudin–Shapiro identity
exactly for `M` up to 2048; the coefficient bounds and the ratio of the step version for `N = 2..32` (ratio 1.19 to
2.83, against the bound `H_N/π − 1/2` of −0.02 to 0.79); and, for `N = 4` and `8`, the continuous phase on the true
box: largest lattice coefficient `4π²/(4N)` (half the claimed bound) and ratio 1.57 and 1.98, with the fractional
integral converged to `10⁻³` under the trapezoidal rule. This checks finite instances only; the divergence rests on
the derivation.

Status. Plant F-a: FALSE on paper (external derivation, checked step by step by the lead, finite instances checked
numerically); not machine-checked. The plant ledger keeps its compiled outcome NOT DETECTED and adds this note
(new file `docs/replay/plants/2026-11-28-K2/followup-F-a.md`; the stamped `README.md` is not changed). A compiled witness is a separate assurance task, not
a dependency of any K2 proof: it needs the Rudin–Shapiro induction, the integrals of a step function against
characters, the `L¹` comparison for the ramps, and the divergence of `H_N`. Not started.
