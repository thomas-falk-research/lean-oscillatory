# CENSUS pre-registration: singularity census of 2D dispersion relations

Status: DRAFT. Not registered; nothing has been run under it. To register: fill every field marked (at registration),
pass the pre-registration referee (§7), replace DRAFT with REGISTERED in this line, commit, push, and record the commit
in `docs/prereg/LEDGER.md`; the run log's first entry repeats the hash. After that only §8 may change.

Target claim class (computation-of-record table): per model, "PROVEN (computer-assisted; two independent
implementations)" for the statements both implementations can decide, and "certified by A only" for the rest (§4).
Verification-ladder rung of every census result: L3 (computer-assisted, tools not verified). Rung required before any
statement "model M is covered by an OscInt theorem": L4 (the classification discharged in Lean).
ASSUMED(L4: Lean discharge of each cited model's classification, through ROADMAP I2 or exact certificates; lead).

- Spec: `docs/prereg/2026-11-09-CENSUS-spec.md`, frozen at commit (at registration), before either implementation
  existed. Symbolic checks of the spec: `numerics/census/spec_checks.py`, output
  `numerics/results-census-spec-2026-11-09.txt` (29/29 PASS at the commit recorded in that file).
- Implementations: A = `numerics/census/impl_a/` (exact algebra, spec §6), B = `numerics/census/impl_b/` (interval
  branch and bound, spec §6), written by different agents; B from the spec alone. Authors (person or model): (at
  registration).
- Acceptance script: `numerics/census/accept.py`, with its negative-control suite `numerics/census/accept_controls/`
  (crafted outputs that must each FAIL: a missing field; `"complete"` absent; `"certified"`-style flags as strings; a
  box with an inverted interval; non-ASCII digits; a top-level list; an A3 point of A inside an EXCLUDED box of B; an
  A3-PROVEN box with no A point; a box set that leaves a gap in the torus; a spec hash mismatch; a wrong git commit).
- Spec-only evaluator for soundness checks: `numerics/census/evaluator.py`, mpmath at 50 digits, written from the spec
  alone by an agent that has not read A or B, before reading them.
- Environment: Python lock with hashes for A, B and the acceptance script; solver and interval-library versions
  (at registration). Common-mode libraries: (at registration; if A's and B's deciding computations share one, the
  two-implementation label is withheld for the affected claims, spec §6).
- Machine: a workstation or server that stays up for the whole run (not a cloud agent container, which is reclaimed
  when its session idles); CPU, OS, image digest (at registration). Estimated run time: from the development runs (at
  registration).
- Budgets: spec §6; A's degree cap per model fixed from the development runs (at registration).

## 1. Disclosure (everything known or run before registration)

Runs on corpus models or controls before this registration, all with their outputs committed:
- P1 (`numerics/results-classify-2026-11-08.txt`): M01 NFD4; M11 (σ = (0.5, 0.3)) NFD4; the cusp control `x²y + y²`
  (K1 before rotation and shift) CUSP. Grid method, which misses sub-grid cusps (lessons 43).
- VV-classify (`numerics/results-classify-vv-2026-11-08.txt`): M07 CUSP; QWZ m = 0.5 CUSP (not in the corpus); M08
  NFD4 (wrong, erratum `docs/design/vector-amplitudes.md` §6); M03 CUSP; K5 CUSP (required "not NFD4").
- VV-qwz-decay (`numerics/results-qwz-decay-2026-11-08.txt`): M08 kernel decay check NOT PASS.
- Exact facts established before this registration (`numerics/census/spec_checks.py`): M01's complete classification
  (four D4 points, folds, no A3; check K-SQ); four A3 points of M08 at `(±arccos(−1/3), ±arccos(−1/3))` (K-QWZ3, first
  found by the VT adversarial referee); the expected outcomes of K1, K2, K3, K5; the NS sets of all corpus models.
- Published classifications read before registration (the logged sweep `review/2026-11-09-CENSUS-prior-art-sweep.md`):
  M17 (Cuenin–Ikromov; Borovyk–Goldberg), M03 (Ge–Hua–Jia–Zhou), M18 (Wan–Zhang); decay-rate papers for M05
  (Hong–Tadano–Yang) and M16 (Schultz; Bi–Cheng–Hua). The corpus was revised after the sweep and before freezing
  (spec §8): M18 added, M11's weight set to 0.
- During the development of `spec_checks.py`, its first run failed three of its own checks (a sign error in R2; K1 and
  K3 decided "g3 = 0" from a zero kernel vector); fixed before commit, recorded in spec §8.
- Development runs of A, B and the acceptance script: (at registration; every rung, including expected failures, run
  once with a small budget, outputs listed here).

Expected outcomes, stated by the lead before any census run (CONJECTURED unless marked; not criteria): M01 GD-covered
(exact); M08 has A3 points (exact); M17 has A3 points exactly at `(±π/2, ±π/2)` and M03, M18 have only A2/A3
degenerate points (literature, spec §5); M07 has A3 points (grid verdict CUSP); M05, M10, M13, M14, M15, M16 are not
GD-covered whatever else holds (NS nonempty, exact); no prediction for M02, M04, M06, M09, M11, M12. Expected ranking:
F-A3 first, F-NS second. The implementers are not told these expectations.

## 2. What the registered run does

From the registered commit, through a wrapper generated by the computation-of-record `make_run_wrapper.py` and
committed with the registration (`numerics/census/run_census.sh`): stops at the first failing step, moves earlier
outputs aside, refuses a dirty tree, prints `STEP_OK`/`STEP_FAIL` per step and `WRAPPER_EXIT rc=… complete=…`. Steps:
1. `spec_checks.py` (must print `ALL_CHECKS_PASS`);
2. the acceptance negative-control suite (every control must FAIL);
3. implementation A on M01–M18 and K1, K2, K3, K5 → `numerics/census/out/a.json`;
4. implementation B on the same → `numerics/census/out/b.json`;
5. the spec-only evaluator on A's reported points and on seeded points (§3, C5) → `numerics/census/out/eval.json`;
6. `accept.py` on the three outputs → `numerics/census/out/verdict.txt` and `numerics/census/out/ranking.json`.

## 3. Criteria (all must hold for PASS; checked by `accept.py`, which recomputes every verdict from the outputs)

- **C0 (acceptance controls).** Every crafted output in `accept_controls/` produces FAIL with a reason.
- **C1 (provenance and completeness).** Each output has `complete: true`, `spec_sha256` equal to the SHA-256 of the
  spec at the frozen commit, `git_commit` equal to the registered commit, `dirty: false`.
- **C2 (controls).** A reproduces spec §5 exactly for K-SQ, K1, K2, K3, K5 (types, locations within the enclosure
  width of spec §4.1, and nothing else in Σ). B: for K1 exactly one A3-PROVEN box, containing r; for K-SQ, K2, K3, K5
  no A3-PROVEN box; every A-object of each control lies in a B box labelled UNRESOLVED or A3-PROVEN (never EXCLUDED).
- **C3 (cross-agreement, every model and control).** (a) B's boxes cover the domain exactly (checked in exact dyadic
  arithmetic). (b) No isolated point of A, and none of the exact sample points A gives for each component (spec §4.1),
  lies in a closed B box labelled EXCLUDED; membership is decided from A's exact description, refining its isolating
  box until it lies inside one B box or inside the interior of a union of B boxes. (c) Each A3-PROVEN box of B contains
  exactly one isolated point of A, of type A3, and no other isolated point or sample point of A.
- **C4 (known answers).** (a) A reports the four A3 points of K-QWZ3, each enclosing `(±a, ±a)` exactly as spec §5,
  and the four A3 points of K-DKG at `(±π/2, ±π/2)`. (b) Literature (spec §5, X-DKG, X-TRI, X-KING): A's classification
  of M17, M03 and M18 agrees with the published statement.
- **C5 (soundness spot checks, spec-only evaluator).** (a) At every isolated point A reports (its exact location
  evaluated at 50 digits), `|det H|`, `|T[v_a³]|`, `|T[v_b³]|` (scaled by `1 + ‖H‖² + ‖T‖³` at the point) are below
  1e−40, and the type-deciding quantity (`g4` for A3, `Disc` for D4) has absolute value above 1e−20. (b) At 1000 points
  per model from the linear congruential generator of `docs/prereg/2026-11-08-VV-classify.md` with seed 20261109, every
  B box containing the point has enclosures of `det H`, `T[v_a³]`, `T[v_b³]` that contain the evaluator's 50-digit values
  (allowance 1e−30).
- **C6 (descriptive, not a criterion).** Per model: the objects found, which implementation decided each, budgets
  used, and B's UNRESOLVED boxes that contain no A-object (B's weakness, not a contradiction).

## 4. Interpretation fixed in advance

- **PASS** → per model M (A `DONE`):
  - "the classification of Σ(Ψ_M) and NS(Ψ_M) reported by A: PROVEN (computer-assisted; single implementation A)";
  - if every B box is EXCLUDED, A3-PROVEN or NS-ADJACENT, or contains an A-object: "outside the reported objects and the
    radius-2⁻¹⁰ neighbourhoods of NS points, every point is A1 or A2, and the A3 points in A3-PROVEN boxes are exactly
    A's: PROVEN (computer-assisted; two independent implementations)", subject to the common-mode rule of spec §6;
  - types of rank-0, A≥4 and non-isolated objects, and A3 points B did not prove: "certified by A only (not claimed
    as two-implementation under this registration)".
- **Ranking and recommendation (fixed now).** From A's classification of the models that pass C3: `N(F)` and `D(F)`
  of spec §4.3 for F ∈ {F-A3, F-NS, F-NI, F-D5, F-A4, F-E}. The lead recommends to the owner the F with the largest
  N(F); ties broken by larger D(F), then by the order just listed. If every single N(F) is 0, the pair with the largest
  N is recommended. VV acceptance candidates: the non-separable models of domains L and T that are GD-covered; if none,
  those covered by GD ∪ {recommended F}. The owner decides; recommendation and decision are recorded in
  `docs/ROADMAP.md` (I3).
- **C0 or C1 fails** → no result; the cause is found and the run repeated under §5.
- **C2 or C4(a) fails** → NOT DISCRIMINATING: no claim for any model; investigate; any fix is a new registration.
- **C4(b) fails for a model** (A and B agree with each other but not with the published statement) → no claim for
  that model; the disagreement is investigated at the level of the exact points (which point, which type) and reported
  either as an error in the implementations (then a fix and a new registration) or as a documented disagreement with
  the paper, sent to the owner before any public statement.
- **C3(b) or C3(c) fails for a model** → soundness conflict between A and B: no claim for that model; investigated and
  reported; the other models keep their verdicts only if the conflict is shown to be local (by the results referee).
- **C5 fails** → no claim for the affected model; investigate.
- **A `BUDGET_EXHAUSTED` on a model** → the model is UNRESOLVED and excluded from N(F) (reported with its weight); B
  `BUDGET_EXHAUSTED` only → A's result stands as "certified by A only".

## 5. Failure rule

- External interruption (process killed from outside: container reclaimed, reboot, power loss, OOM caused by other
  load): no result; logged in §8 with evidence; rerun unchanged; not counted.
- Transient crash (exception or resource failure that may not recur): logged with the traceback; one unchanged rerun.
- Deterministic bug: logged with the traceback; minimal fix committed separately; the diff over all executed code shown
  to be the fix; a fresh fix referee decides whether it touches a criterion or could change a verdict; the owner
  authorises; one repeat from the fix commit. No criterion changes.
- Partial or stale inputs: any verdict printed from them is void; such outputs are kept as `attemptN_…`.
- Anything not covered here is decided by the owner and logged in §8 as a deviation that names what it supersedes.

## 6. Post-run checks

Commit and dirty flag in every output; comparison with the development smoke test (timing keys ignored); `accept.py`
re-run on a second machine; a falsification pass by a fresh agent (spec-only evaluator first, then adversarial search
near every reported object, on symmetry lines and near NS points), its scripts and outputs committed under
`review/census-falsification/`; a results referee (fresh context) recomputing every verdict from the output files.

## 7. Referee

Pre-registration referee (fresh context; preferably a different model family or a human): report at (at registration),
verdict, each finding and what was done about it. Spec-fidelity referee of the spec: see the spec's status line.

## 8. Run log

(empty: not registered)
