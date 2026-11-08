# Answers to the blind pre-proof reviews of front-end batch 3 (API3)

Reviews: `review/2026-11-08-API3-pre-proof-A.md`, `review/2026-11-08-API3-pre-proof-B.md` (verbatim; both on
e42dcd3, the commit pinning stamp `stamps/20261108T002603Z-9d03130c8f3a`; prompt `review/prompts/API3-pre-proof.md`).
Both referees state that they proved nothing and wrote nothing in the repository.

Verdicts: FAITHFUL and TRUE for all ten statements, from both referees; no counterexample; no BLOCKER. The stamped
statement file `OscInt/Statements/Family.lean` is unchanged.

## M1 (both referees, MAJOR): the sanity theorems restate the hypotheses (lessons 11) and do not separate the new
features (critical points only; the sign of `p`/`L`; S ≠ V, K ≠ U)

Agreed. The finding concerns the test layer, not what the statements mean: both referees judge every statement
faithful and true, and referee A recommends recording it and testing through the statement constants. Rule applied:
CONTRIBUTING step 5 ("A BLOCKER or MAJOR means a new statement, never an edit") exists so that a statement that says
the wrong thing is never repaired in place; here no statement is wrong, and re-freezing the same ten texts with
hypotheses bundled as `def`s would change nothing they say. I therefore do not re-freeze; this reading of the rule is
put to the adversarial referee of this batch, and the owner may overrule it (then API3′ is a new statement batch with
bundled hypotheses).

What is done instead, before any proof exists: `OscInt/Front/FamilySanity.lean`. Each theorem there takes the
statement constants as hypotheses (it proves nothing about them) and instantiates them on data chosen so that the
discharge of the statement's hypotheses breaks under the plants the referees named:
- `foldCrit_fold_bite` (referee B's data: x³ + y³, K = B̄(0, 2), K′ = {(0, −3)}): critical points (0, ±1) are folds;
  0 ∈ K is degenerate but not critical. Breaks under `p ↦ 0` and under "fold condition at every k ∈ K". Neither S2.2
  nor S3 gives this bound.
- `stationaryPhaseFamily_sign_bite`, `foldCrit_sign_bite` (referee B's sign pin, on the infinite family
  σ(k₁⁴ + 4k₁) + k₂², σ ∈ [1, 2], with `FamilyCk` obtained through C10's constant): break under `p ↦ −p` and under
  "everywhere"; the `p ↦ 0` plant is caught for S3c by the first theorem, and the docstrings say which plant each
  theorem does not catch.
- `stationaryPhaseOn_kink`, `foldOn_kink` (Mathlib idiom, through `StationaryPhaseOnStatement`, `FoldOnStatement`):
  a phase equal to k₁⁴ + 4k₁ + k₂² on U = {k₁ > −3} and not C¹ on ℝ², K = B̄(0, 2) ⊊ U, K′ = {4·fst}; pins `+ L` and the
  e₀/e₁ order.
The file is compiled by `make quick` like every library file; a plant in a statement body that these data detect
makes it fail. Plants these data do not detect are listed in the file's docstrings.
Delivered: all six (`foldCrit_fold_bite`, `stationaryPhaseFamily_sign_bite`, `foldCrit_sign_bite`, `stationaryPhaseOn_kink`,
`foldOn_kink`, `familyCkOfUncurry_nonconst`, with `kinkPhase_not_contDiff`). Negative controls run by the lead: four plants
(`p ↦ −p`, `p ↦ 0` in S3c; `+ L ↦ − L`, "everywhere" in FE-S2.2l) each break the matching theorem, unplanted copies
compile (`docs/replay/2026-11-08-API3-sanity-plants.txt`). Not caught by these data: `p ↦ 0` in S2.2F, `L ↦ 0` in FE-S2.2l/S3l.

## Other findings

- B MINOR 2 (S2.2F does not follow from the frozen S2.2/S3; it needs the internal parts): agreed; the route
  (`docs/proof-API3.md`, R1) re-assembles the proved internal parts, and no document claims S2.2F follows from the
  frozen statements alone.
- B MINOR 3, A m1 (bites too weak): answered by the theorems above.
- B MINOR 4 (the S2.2F witness is a finite family at p = 0, k = 0): answered by the infinite-family theorems above
  (σ ∈ [1, 2], p = (4, 0), critical x ≠ 0).
- B MINOR 5, A m3, A m4 (C10 needs global smoothness on E × ℝ²; the FE-L forms ask for joint C^n in σ, more than
  `FamilyCk`; no local analogue of C10): agreed, recorded as candidates for the next batch (a `ContDiffOn` C10 on
  V ×ˢ univ; a local C10 for families only continuous in σ, e.g. the rescaled family of S4). `docs/statements.md` gets a
  clarification that C10 serves globally smooth families and is not used by the FE-L forms (which use a cut-off).
- A m2 (no sanity at the level of the FE-L/l hypotheses): partly answered by the kink theorems (FE-S2.2l, FE-S3l);
  derivative-level checks of FE-S2.1L/S2.2L/S3L with S ⊊ V and of FE-S4.1′L on a generic cubic follow after the
  proofs, through the bridges (the referees' lists (a)–(f) and B's list are recorded as the post-proof checklist).
- A N1, B NIT 6 (`Metric.ball` on ℝ × ℝ is a square): the hemisphere consumer example will use the Euclidean disc
  `{k | k.1 ^ 2 + k.2 ^ 2 < 1}` and say why.
- A N2 (the local-smoothness gain is in what the user proves, not in mathematical reach): agreed; the clarification
  says so.
- A N3 (FE-S3L's "matrix form" is the span form): agreed; clarified in docs.
- A N4 (universe 0): as in the frozen statements; harmless.
- B NIT 7: the S3c bite's docstring is in the stamped file and cannot change; the clarification notes that S2.2 gives
  that bound, and the new `foldCrit_fold_bite` is the bite that neither S2.2 nor S3 covers.

## Order of work
No Lean proof of an API3 statement exists. The route `docs/proof-API3.md` was drafted in the lead's scratch during
the review window (no Lean proof code; disclosed in its header). `FamilySanity.lean` was written after the reviews
and before any proof, by a sanity agent under `review/prompts/API3-sanity-brief.md`. The reviews, these answers, the
route and the sanity file are committed and stamped before any proof agent starts (lessons 29).
