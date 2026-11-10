# Answers to the blind pre-proof reviews of front-end batch 2 (API2)

Reviews: `review/2026-11-07-API2-pre-proof-A.md`, `review/2026-11-07-API2-pre-proof-B.md` (both on commit 9385017,
prompt `review/prompts/API2-pre-proof.md`). Verdicts: FAITHFUL ×2 on all fourteen statements; no BLOCKER, no MAJOR.
The stamped statement file `OscInt/Statements/Convert.lean` is unchanged; nothing below edits it.

## Disclosure (referee A)
Referee A proved C5 (`DiscEqCubicDiscrStatement`) in its own scratch directory while checking truth
(`simp only [disc, Cubic.discr]`). That proof was written by a referee, after the stamp, outside the repository, and
never seen by the lead before the reviews were in. The claim made for batch 2 is therefore: **no proof of any batch-2
statement existed in the repository or in the lead's scratch before the stamp and the two reviews**; one referee
wrote a one-line proof of C5 during its review. The lead's C5 proof is written independently (it is the same
unfolding).

## Dispositions
| Finding | Disposition |
|---|---|
| A-MINOR 1, B-MINOR 3, B-MINOR 4, A-NIT 4, A-NIT 7, A §5 (derivative-level and asymmetric sanity) | Accepted. `OscInt/Front/ConvertSanity.lean` (new, not a statement file; written while the proof agents ran, not before them as first stated here — corrected after the adversarial review, M3) adds: `hessianMatrix` of a phase with distinct, nonzero mixed entries; `FoldOrNondegMatrix` of the fold x³ + y² at every point; the FE-S4.1′ identity for a generic cubic plus a bite with the reversed coefficients; a non-symmetric kernel witness pinning `toLin'` as the right kernel; a C6 bite on the derivative side; the written-out amplitude bound `Iff.rfl` `AmpBound`. These use only the session-2 internal lemmas and Mathlib, never a batch-2 statement. End-to-end front-end instances follow after the proofs (consumer example). |
| A-MINOR 2, B-MINOR 2 (C7′ could assume `∀ᶠ y in 𝓝 k`) | Agreed it is stronger and still true. Not an edit: recorded as a modelling choice in `docs/statements.md` (clarification below) and as a candidate statement for the next batch (ROADMAP §2). |
| A-MINOR 3, B-MINOR 1 (no `HasFDerivAt`-data route for D², D³ identities; C7′ concludes `FoldOrNondeg`, not `FoldOrNondegMatrix`) | Answered by tooling, not a statement: the P2 helpers `OscInt/API/Poly.lean` compute `D^nφ(k)[v,…,v]` from a polynomial expansion of `t ↦ φ(k + t v)` (proved, unfrozen, they only produce hypotheses). A frozen "C1′/C2′ from derivative data" is a candidate for the next batch. |
| A-NIT 5 (`‖L‖ = \|L e₀\| + \|L e₁\|` asserted but not provided) | Accepted: `OscInt.API.NormAux.norm_prod_functional` (an equality) in `OscInt/Front/ConvertNorm.lean` (corrected after post-proof B, NIT 1). |
| A-NIT 8 (glue `fderiv (Ψ + lin p) k = fderiv Ψ k + L`) | Accepted: a named lemma in the bridges. |
| B-NIT 1 (`↑N + 1` vs `↑(N + 1)`) | Noted; handled in the bridge by `Nat.cast_add`. |
| B-NIT 2 (`disc` is invariant under (a, b, c, d) ↦ (d, c, b, a)) | Accepted: one sentence in the clarification below; the coefficient order is pinned by the derivative-level sanity theorem with a non-palindromic cubic. |
| B-NIT 3 (C7′ name suggests one direction) | The statement is an iff, as its docstring formula shows; name kept (renaming means a new statement). Documented below. |
| A-NIT 6 (C5 is definitional) | Agreed; harmless. |

## Clarification added to `docs/statements.md`
See "Clarification added after the API2 stamp (2026-11-07)".
