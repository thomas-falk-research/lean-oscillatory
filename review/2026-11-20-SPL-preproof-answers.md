<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL: answers to the blind pre-proof reviews (2026-11-20)

Written by the lead. Step 5 of `CONTRIBUTING.md`, quoted before it is applied (lesson 66a): "Two fresh-context
referees review the statement against `docs/statements.md` without seeing any proof. … A BLOCKER or MAJOR means a
new statement (back to 2), never an edit. A MAJOR whose finding is only against the prose of `docs/statements.md`
(not the Lean text, not the sanity layer) is answered by a dated clarification there".

Reviewed: the four statements of `OscInt/Statements/StationaryLeading.lean`, frozen text SHA-256
12f8d3b622949cd8a9d3d518236da7f96ae84cc26f3d72dda64bb05bfb40c715, stamped
`stamps/20261120T002727Z-5491b10bc8ae` (00:27:34Z), against the section "Batch SPL" of `docs/statements.md` as of
bd91881. Two referees from fresh contexts, both of the lead's model family; briefs' SHA-256 in the session log;
launched after the stamp and after the launch was logged and pushed (4d1f955). The reports are not reproduced;
every finding is in the lead's words.

Blindness, and its limits. The referees worked from a packet outside the repository (statement file, prose
section, sanity file, plant record) and were told which files they might open and which not (the proof page, the
design notes, the reviews, the logs, the status page, the prior-art page, the numerics). Each listed the files it
opened; neither list has a forbidden file. This is blindness by instruction and by self-report, not by a
sandbox. Three things they could see or infer: the prose says that a proof on paper, a registered test and
external sessions exist; referee A read the head of `CONTRIBUTING.md`; referee B derived the identity on its own
(asked to), which is its derivation, not the lead's. No Lean proof of a statement existed when they ran.

**Result: no BLOCKER and no MAJOR finding, from either referee, against the Lean text, the prose or the sanity
layer. Step 5 asks for no new statement. The statements stand as frozen.**

## Referee A (fidelity)

Verdicts: SPL-I, SPL-S, SPL-K, SPL-A each FAITHFUL. Method reported: a compiled probe in which every definition
and statement, re-typed with full parentheses and explicit measure, closes by `rfl` (with a negative control that
fails); the exponent is `Real.rpow lam ((−3)/2)`; `∞` is the smooth index, not the analytic one; the junk values
of the Bochner integral, of `0 ^ (−3/2)` and of `√(2π/0)`; its own numerics at 25 digits of the identity on five
amplitudes with the kernel transcribed from the Lean text; 13 witness files read, six compiled.

| # | Severity, target | Finding (lead's words) | Answer |
|---|---|---|---|
| A1 | MINOR, sanity layer | No planted mutation touches the inside of `splKernelPos`, `fresnelPrim`, `fresnelLimit` or the phase inside `splRemainder`; "none undetected" reflects the 42 mutations chosen. It lists uncovered mutations and says for each whether the existing data could detect it (a sign or coefficient inside the kernel: no; the phase `λu²/2 ↦ λu²` or the sign of `i` in the remainder: yes, not planted; `fresnelLimit` altered: only relative to SPL-A with SPL-K; `0 < ε ↦ 0 ≤ ε` in SPL-A: no; `Integrable g₃` dropped: no; 7/8 ↦ 0.7: no). | Accepted as a limit of the layer, not repaired before the proofs: the layer was frozen with the statements, and a MINOR does not reopen it. The list is recorded in `docs/statements.md` (clarification SPL-c). The inside of the kernel is covered by other evidence, each of which is weaker than a Lean witness: the registered numeric test, the two referees' own numerics, and an independent derivation by another model family. After the proofs, the conditional witnesses become unconditional and the proof of SPL-I fixes the kernel. |
| A2 | MINOR, process (the Lean file) | The frozen statement file has no copyright header, although `CONTRIBUTING.md` says a new statement file carries one inside its frozen bytes. | True: a rule the lead missed. The frozen bytes cannot be changed. Remedy within the rule's own exception: the fixed attribution block is appended to the statement file and to the challenge file (the tools hash the bytes before it; the frozen SHA-256 values are unchanged: 12f8d3b6…b40c715 and d58154f9…4c217c2d). The owner was told in the session before this was done and may decide otherwise. |
| A3 | NIT, sanity layer | No mutation of the sign, exponent or kernel argument of SPL-I is refuted unconditionally; before a proof the evidence that the frozen SPL-I is the true variant is numeric. | Agreed; it is what the plant record says ("relative to the true statement"). |
| A4 | NIT, prose | SPL-I equates two Bochner integrals and does not assert that the integrand on the right is integrable; item 4 speaks of junk values only for the left term. | Clarification SPL-a. |
| A5 | NIT, prose | "Each statement is instantiated at two Gaussians" is not true of SPL-A. | Clarification SPL-b: SPL-A is instantiated at τ = 0 and τ = 1, with no Gaussian datum. |
| A6 | NIT, prose | Item 8: "since \|g″(0)\| ≤ ‖g₃‖₁/2, no constant below √(2π)/4" does not follow as worded (it needs amplitudes close to equality); the number is right. | Clarification SPL-b. |
| A7 | NIT, prose | "The best constant is sup \|κ\|" is not a Lean statement; it needs `‖g₃‖₁ > 0` for a nonzero amplitude (proved in the sanity layer) and concerns constants uniform in λ. | Clarification SPL-b. |
| A8 | NIT, Lean | Redundant, harmless clauses in SPL-A: `0 ≤ τ`; the integrability clauses of `SplAmplitude` (implied by smoothness and compact support). | No action. |

## Referee B (truth)

Verdicts: NO COUNTEREXAMPLE FOUND for each of the four. Method reported: Lean semantics by reading Mathlib (no
compilation); its own derivation of the identity by three integrations by parts with primitives vanishing at
infinity, agreeing with the Lean text in sign, constant, power, kernel argument and odd extension; numerics of
its own on ten amplitudes and six values of λ from 0.05 to 500, both sides computed independently (largest defect
3.4 · 10⁻¹²), among them a complex amplitude, a C³ function that is not C⁴, a slowly decaying one, and two whose
third derivative is discontinuous or unbounded at a point; `sup |κ|` = 0.721973999 at 1.62460062; a near-extremal
amplitude reaching 99.79 % of it; an argument that SPL-A cannot fail for any τ and ε.

| # | Severity, target | Finding (lead's words) | Answer |
|---|---|---|---|
| B1 | MINOR, Lean and prose | The class excludes amplitudes whose second derivative has a corner (cubic splines, piecewise C³ functions): `HasDerivAt g₂ (g₃ x) x` at every point forces the intermediate-value property of `g₃`, so `g₃` cannot jump, although the identity holds for such amplitudes. Prose item 3, "continuity of g₃ is not asked", can be read as admitting jumps. | True, and worth knowing for a user: the statements are for derivatives that exist at every point. Clarification SPL-a says so; a version for a second derivative that is absolutely continuous is a possible later statement. Not a defect of fidelity: the prose's definition of an amplitude says "at every x". |
| B2 | MINOR, sanity layer | All data of the sanity layer are real, even Gaussians with `g(0) = 1`; no plant mutates the factor `g 0` (to 1, to a conjugate, to a modulus) or the inside of the kernel; on complex or non-even amplitudes such mutations are invisible to the layer. | Accepted as a limit, as A1; recorded in clarification SPL-c. The referee's own numerics cover complex and non-even amplitudes. |
| B3 | NIT, Lean | Any constant in [0.722, 0.875) in SPL-K is equally true and unseen. | Known and stated (item 6 of the prose). |
| B4 | NIT | The packet's plant record is the repository summary with a header. | Yes: it is `docs/replay/2026-11-19-SPL-sanity-plants.txt`. |

## What follows

- The statements stand. `docs/statements.md` gains clarifications SPL-a, SPL-b, SPL-c (prose only).
- The attribution block is appended to the two Lean files (A2).
- These answers are stamped before any Lean proof of the batch enters the repository.
- Not established by this review: truth by proof; anything about the kernel's supremum in Lean; fidelity as a
  human expert would judge it. Both referees share the lead's model family; the one review of these statements by
  another family (before the freeze, `review/2026-11-19-SPL-external-sessions-answers.md`, section 5) reached the
  same four verdicts.
