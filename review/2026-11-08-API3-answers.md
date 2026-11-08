# Answers to the post-proof and adversarial reviews of front-end batch 3 (API3)

Reviews (verbatim, all on 11a9ecf, the commit after the replay record of a638f70): `review/2026-11-08-API3-post-proof-A.md`,
`review/2026-11-08-API3-post-proof-B.md`, `review/2026-11-08-API3-adversarial.md`; prompts in `review/prompts/`.
No referee wrote in the repository. The statements, proofs and stamps are unchanged by everything below; the changes
are sanity theorems, a consumer example, the release-pin tool and records.

## Adversarial review

**Verdicts.** (a) holds with qualifications (all ten proved, statements unchanged since the stamp, both stamps sound,
no proof file in either manifest); (b) partly holds; (c) holds for tag pins, not for raw commit pins.

**M1 (MAJOR): five constants had no sanity theorem through the constant.** Agreed. Added
`OscInt/Front/FamilySanity2.lean` (sanity agent 2, brief `review/prompts/API3-sanity2-brief.md`): every theorem takes
the statement constant as a hypothesis and applies it to data:
- `nonStationaryLocal_family` (FE-S2.1L): the arccos family over `S = B̄(0, 1/4) ⊊ V = {|a| + |b| < 1}`, `U = ℝ²`;
- `stationaryPhaseLocal_kink`, `foldLocal_kink` (FE-S2.2L, FE-S3L): the kink phase as a family with `S = {1} ⊊ V = (0, 2)`;
- `d4BoundLocal_kink` (FE-S4.1′L): the generic cubic x³ + 2x²y + 3xy² + 5y³ plus a kink on x = 5 (not C¹ on ℝ²);
- `nonStationaryOn_kink` (FE-S2.1l).
All ten statements now have at least one such theorem. Each docstring lists the plants caught and the plants not
caught. A structural limit, stated in the file header and here: a conditional sanity theorem detects only a plant
that makes a hypothesis harder to discharge (or the conclusion weaker); a plant that WEAKENS a hypothesis (e.g. the
referee's `V ×ˢ U ↦ S ×ˢ K`, a dropped hypothesis, C⁴ lowered to C³) makes the discharge easier and is not detected.
Such plants change a statement into a stronger and possibly false one; they are left to the blind fidelity reviews
(pre-proof ×2, post-proof ×2) and to the stamp, which fixes the text the reviews read.

**M2 (MAJOR): the sign bites ignore `k ∈ K`.** Agreed, and reproduced. Added `stationaryPhaseFamily_binder_bite`:
Ψ = k₁⁴/4 − 2k₁³ + 9/2·k₁² + k₂², K = B̄(0, 1), K′ = {(0, 0), (3, 0)}; with p = (0, 0) the point (3, 0) is a degenerate
critical point outside K. Controls (`docs/replay/2026-11-08-API3-sanity-plants.txt`, second part): the referee's
two S2.2F plants (`∀ k ∈ K ↦ ∀ k ∈ univ`, `↦ ∀ k, k ∈ K′`) are now rejected, the unplanted copy compiles. For S3c the
same data do not catch the plant ((3, 0) is a fold: Hessian diag(0, 2), ∂₁₁₁Ψ = 6); S3c's `k ∈ K` binder is caught by
`foldCrit_fold_bite`, whose binder is typed (`k ∈ closedBall 0 2`), as the referee noted.

**Erratum (2026-11-08, session 6).** The "second part" of `docs/replay/2026-11-08-API3-sanity-plants.txt` cited
under M2 never existed (one commit, one part; step-5 rule referee, finding 2). The M2 plant sources were in
`docs/replay/plants/2026-11-08-API3/{Kprime,univ,ok}-binder.lean.txt` with the outcome only in the ff5b80e commit
message; they were re-run and recorded in `docs/replay/2026-11-08-session6-API3-plants-rerun.txt`. The M2 text above
is kept as written.

**M3 (MAJOR): not re-freezing departs from CONTRIBUTING step 5.** Agreed that it is a departure from the written rule,
and it stays one until the owner decides. What changed since the referee read it: the substitute now covers all ten
constants (M1) and the demonstrated M2 plants, with the limit above stated. The documents no longer say the MAJOR is
"answered"; they say "addressed by conditional sanity theorems, pending the owner's decision on CONTRIBUTING step 5".
Owner decision (HANDOFF, "Owner decisions"): (i) ratify an amended step 5 — "a MAJOR confined to the test layer (sanity
theorems), with every statement judged faithful by both referees, may be answered by sanity theorems through the
statement constants covering every statement, with planted controls"; or (ii) re-freeze the ten texts as API3′ with
hypotheses bundled as `def`s (lessons 11), reviewed and proved again (the proofs carry over). The lexical check of
lessons 11 is not implemented (ROADMAP §4).

**m1 (MINOR): raw commit pins were not checked.** Fixed: `tools/check_release_pin.sh` check 5 requires every raw
40-hex pin to be a commit contained in HEAD (which implies it exists). Self-test cases added (a commit pin not in HEAD
is rejected; one in HEAD is accepted).

**m2 (MINOR): the self-test never ran the real ancestry predicate.** Fixed: the self-test builds a three-commit git
repository and runs the real `in_head` (rejects an unmerged commit, accepts it after the merge, rejects a nonexistent
commit). Negative control: with `in_head` replaced by `… || true`, the self-test fails twice (`release-pin self-test:
FAIL (2)`), so a regression of that kind is caught.

**m3 (MINOR): the order claim is stronger than the stamps.** Agreed. `docs/statements.md` (batch 3, "Order") and the
pre-proof answers are worded as: "no proof was committed before the review stamp (01:05:48Z); that none existed in
scratch rests on the lead's statement; the scratch birth times observed by the adversarial referee (first proof file
01:06:25Z) are consistent with it but not durable evidence".

**m4 (MINOR): plant files not in the repository; controls show brittleness, not semantic detection.** The plant files
are committed under `docs/replay/plants/2026-11-08-API3/`. On semantics: agreed and already stated in the record
(VALIDATED for the proof script, CONJECTURED-by-hand for the falsity of the planted hypothesis on the data).

**m5 (MINOR): stale prose.** Fixed in the records commit: STATUS rows for the ten statements, HANDOFF rewritten for
session 5, CHANGELOG "Unreleased" lists the statement changes and v0.3.0 as published, the session checklist updated.

**n1, n2 (NIT).** n1: acknowledged (stamped file). n2: the 200-byte OpenTimestamps file is a pending attestation like
the others' initial state; RFC 3161 ×3 carry the claim; upgrading OpenTimestamps proofs is ROADMAP §6.

## Post-proof reviews
Both referees: all ten FAITHFUL, scope full, no BLOCKER, no MAJOR; type checks and axiom audit reproduced at 11a9ecf
(37 TYPE-OK; AUDIT-TOTAL 720 720); stamp hashes reproduced; each proof goes through the frozen or proved results the
route names (S2.1 `OscInt.nonStationary`, the internal S2.2/S3 parts, FE-S4.1′ `d4BoundFE`, C3, C7, C8, the cut-off).

- A MINOR 1, B MINOR 2 (derivative-level checks of the local forms not delivered; FE-S2.1L/l, FE-S2.2L, FE-S3L,
  FE-S4.1′L not witnessed beyond trivial data): delivered after the reviews — `OscInt/Front/FamilySanity2.lean` (all
  five through their constants, with S ⊊ V families and phases not C¹ on ℝ², the generic cubic for FE-S4.1′L) and
  `examples/consumer/ConsumerLocal.lean` (the arccos dispersion family over a compact parameter set inside
  {|a| + |b| < 1}, smoothness only through `Real.contDiffOn_arccos`, by the proved FE-S2.1L; the kink phase by the
  proved FE-S2.2l, FE-S3l). Still open: the hemisphere on the Euclidean disc with a non-symmetric K′, and the arccos
  phase through FE-S2.2l at a critical point (Hessian of arccos) — both recorded in HANDOFF.
- A MINOR 2, B MINOR 3, A NIT 5 (non-vacuity and plant falsity only on paper): `examples/consumer/ConsumerLocalChecks.lean`
  is referee A's scratch file, added unchanged except for its header and `#print` lines (disclosed in its header): it
  proves that critical points exist in K for the fold bite, the sign family (intermediate value theorem) and the kink,
  that the S2.2- and S3-type hypotheses fail on the fold bite, that the `p ↦ 0` and `−p`/`−L` planted hypotheses are
  false on the data, and applies FE-S2.2L to a family not C¹ on ℝ² and FE-S3l through the fold (rank-one) branch of
  `FoldOrNondegMatrix` (A NIT 4). With it, the "plants caught" claims of `FamilySanity.lean` for those data are
  machine-checked in both halves (the proof script breaks, and the planted hypothesis is false). `make quick` compiles it.
- B NIT 1 (the sanity theorems stay conditional): `ConsumerLocal.lean` and `ConsumerLocalChecks.lean` instantiate them
  with the proved theorems.
- A MINOR 3, B MINOR 1 (no STATUS rows): added; the replay record is
  `docs/replay/2026-11-08-session5-API3-verify-all.txt` (a638f70; HEAD differed only in records and prompts).
- B NIT 2 (S2.2F/S3c are proved results of this batch, not frozen inputs): the docstring of `OscInt/Front/Local.lean`
  says "the re-assembled S2.2F/S3c"; STATUS states the dependency.
- A NIT 6 (record on a638f70): stated; the commits after it change no Lean file in the proof (sanity and examples only;
  `make quick` re-run on the final commit, CI `verify` on the pushed head).
- A NIT 7: as recorded before (universe 0; C10 not used by the FE-L forms).
