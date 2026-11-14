# Roadmap

From a machine-checked research library to one that others can depend on: correct, usable, maintained, citable.
Items are in priority order within each section; sections are in the recommended order of work. Tick an item only
when its evidence exists (a committed record, a green CI run, a merged change), as in `docs/STATUS.md`. Items marked
**owner** need a decision or an action by the owner.

Downstream feedback (2026-11-06, from an independent session working in the same domain that could use the
library) is folded in below; items it raised are marked *(downstream)*. Its top five, in its order: explicit
constants for the 2D results; local smoothness hypotheses; asymptotic expansions; parametric uniformity everywhere;
a stable way to depend on the library. It asked not to change the trust chain.

## Session-7 order (owner, 2026-11-08)
Agreed in chat after reconciling the session-6 brief with an external review of `main` at 96f55a2. Research, in order:
0. Session-6 review follow-ups: `stamp verify` over every stamp directory (a1), no `.blob` files in stamp directories
   (f4), hash-locked pip installs (f5), a GD-N sanity datum smooth only on U (b2).
1. **Batch LE**: explicit constants for the 1D lattice kernel, pre-registered; by the factorisation
   (`docs/prior_art.md`, "Lattice kernels") they give the 2D constant of T6 as `C₁²`. Landau's constant is the external
   reference; certified numerics (P6) fold in as the independent comparison.
2. **Batch VV**: vector-valued amplitudes, done only when a non-separable model compiles end to end; fallback a
   finite-dimensional componentwise corollary. The vector-valued transfer is done (batch VT). No acceptance model yet: QWZ (m > 2)
   has exact cusp points (erratum, `docs/design/vector-amplitudes.md` §6), QWZ m = 1, 0.5 and the triangular lattice
   have cusps. Next steps (model search done properly, closed-form classification, or Strichartz first):
   `docs/design/vector-amplitudes.md` §7.
3. Strichartz estimates, non-endpoint (TT*), planned over 2–3 sessions: blueprint, prior-art sweep, frozen statement first.
4. The D4 bound uniform over compact families (read Karpushkin and Duistermaat 1974 first), then the arccos family.
Usability, in order: a reusable `oscint-verify` action and Lake template; doc-gen4 site with `llms.txt` from
`docs/api.json` (MCP server postponed); the `HasOscDecay` facade, each lemma an `Iff` with a frozen statement or frozen
itself; `oscint check` as a Python package; one Mathlib pull request (non-stationary phase); a Mathlib compatibility
matrix after the release. Developer experience: `make ci-dry`, the statement-closure diff tool, linters (SPDX outside
`Challenge/`, docstrings), elaboration times in CI, an opt-in pre-push hook. Human expert review: deferred under
`docs/policy.md`.

## Industry programme (owner, 2026-11-09)
Agreed in chat after an external strategy review of `main` at 87a418a and the lead's answer to it. The owner's goal:
a library and toolchain for the whole industry, not for any single consumer. Two rules follow. **Which theorems come
next is decided by evidence across many models** (item I1), not by one model or one user. **The interface is frozen
only after consumers from different domains have used it** (item I5). Items I1–I3 run in parallel; none waits on
another. Nothing here is a capability until its evidence exists (`docs/STATUS.md` rule above).
- [x] **I0 Release reconciliation.** v0.4.0 is published (tag → 87a418a, Zenodo 10.5281/zenodo.24088811). The
      `post-release` pins pull request (#9, merged as 87051c9) and the DOI record pull request (#10, merged as 621cdbe)
      are on `main`. #10's `verify` run on its final head (run 42667383698) passed all 17 jobs, but its `verdict`
      job was never created and the run is marked failed with no failed job (GitHub refused a re-run); the owner merged
      it on those 17 jobs. The `verify` run on `main` after the merge is the check of the merged tree.
- [ ] **Release v0.5.0** (prepared 2026-11-13, owner publishes): batches A3, LE2 and HC, plus the stated LS batch
      (`docs/release-notes/v0.5.0.md`; `tools/release_preflight.sh 0.5.0` passes on the branch).
- [ ] **I1 Singularity census of industry dispersion relations.** Which degenerate points (A3 cusps, A≥4, D4, D≥5, E/J,
      non-isolated sets, non-smooth points) occur in 18 2D models (nine weighted families, plus one unweighted re-check) across five domains (lattice materials,
      two-band topological models, quantum walks, numerical schemes, lattice waves), classified exactly by two
      independent methods with controls. Specification `docs/prereg/2026-11-09-CENSUS-spec.md`; registration draft
      `docs/prereg/2026-11-09-CENSUS-prereg.md` (registered only after both implementations exist and their development
      runs are disclosed; no run before). Its pre-fixed decision rule ranks the candidate theorem families by the
      number of models each one unlocks. It replaces the ad-hoc model search of `docs/design/vector-amplitudes.md`
      §7 option A as the way to choose the VV acceptance model.
- [ ] **I2 LeanCert integration experiment** (independent of I1 and I3). Question: can an external proof-producing
      numerics library discharge OscInt hypotheses for a concrete admissible phase without weakening the trust chain?
      Pins: LeanCert `44b323a0d6af00211d5013f6e021432db032087c` (HEAD on 2026-11-09; same Lean v4.35.0 and Mathlib
      `56a0058` as OscInt, VALIDATED from its `lean-toolchain` and `lake-manifest.json`), OscInt v0.4.0 (87a418a).
      Tests: A, a trigonometric derivative bound on a rational interval; B, a critical-point exclusion on a box, with
      a deliberately false exclusion that must fail or stay unresolved; C, a cusp-classification component (positive
      transverse curvature and nonzero reduced quartic on a neighbourhood). Pass means: each result is a Lean theorem
      checked with LeanCert's `kernel` mode only (`native` and `auto` are recorded as separate, weaker benchmarks); its
      axioms are within OscInt's audit allowlist; the per-module kernel replay of `verify-all` accepts it; cost (time,
      memory, proof size) recorded against a hand proof. A separate pre-registration comes before the first run. No
      copy of LeanCert's engine into OscInt unless a limitation is demonstrated.
- [ ] **I3 Theorem programme, ordered by I1** (provisional until I1's result): a general k-th-order van der Corput
      bound (only k = 1, 2, 3 exist: S1.1–S1.3); the local A3 bound `t^{−3/4}` uniform in the linear term (route to be
      chosen at registration: transverse stationary phase plus fourth-order van der Corput, or a parametric normal
      form); global assembly with finitely many A3 points; leading terms with remainders (SAR and seismic steps use the
      leading term); nondegenerate stationary phase in dimension n; non-endpoint Strichartz; the Ikromov–Müller
      height bound, which covers broad classes of finite-type 2D singularities (exact hypotheses not yet read; the external
      audit reports an exception involving an unbounded principal Newton face, CITED-UNREAD,
      `review/2026-11-10-external-audit-answers.md`), with the A3 statements shaped to be derivable from it. Every batch statement-first under `CONTRIBUTING.md`.
      **Owner decisions 2026-11-10 (order inside I3):**
      1. The A3 formalisation comes first: S5.1′, then S5.1 by weakening, along the reviewed hand proof
         (`review/2026-11-10-external-results-answers.md`).
      2. Then I3a.
      3. Then I3b (the dimension-generic track).
      This revises the morning's order, which put I3a first. Background:
      `review/2026-11-10-external-dossier-answers.md` and `docs/HANDOFF.md`, session 9.
      *Done 2026-11-13:* the general k-th-order van der Corput bound (S1.k) and the local A3 bound t^{−3/4} uniform in
      the linear term (S5.1, S5.1′) are machine-checked as stated (batch A3; replay
      `docs/replay/2026-11-13-session10-A3-verify-all.txt`). Open in I3: global assembly with A3 points, I3a, I3b.
      Batch LS (the free lattice Schrödinger group, ROADMAP "Candidates", the discrete NLS row) is proved in Lean
      (2026-11-14; build, axiom audit, per-module leanchecker; AI-drafted parts, `review/2026-11-14-external-R4-answers.md`);
      its isolated replay and post-proof reviews are pending.
  - [ ] **I3a Parametrised transverse stationary phase, transverse dimension n.**
    - *The lemma.* Take a phase `F(s, u) + y·(s, u)` with `s ∈ ℝⁿ` and `u ∈ ℝ^r`, whose s-Hessian is invertible on
      the amplitude's support. The lemma says the s-integral equals its stationary-phase leading term plus a remainder
      `O(t^{−n/2−1})`, uniformly in the linear term `y`. The leading term is `e^{itF̃(u, y)}` times an amplitude in
      `u` with tracked C² bounds.
    - *Why an expansion, not a bound.* The reduced u-integral must keep its oscillation, so it can be bounded by S1.k
      or by a 2D bound.
    - *Why first (as decided 2026-11-10), and what changed the same day.* The decision assumed S5.1′ needed this lemma
      with `n = r = 1`. The external results of 2026-11-10 show it does not.
      - A hand proof of S5.1′ (hence S5.1) uses the *exact* dephased transverse integral, which is already proved
        infrastructure in `OscInt/StationaryPhase/Core.lean`, with one derivative and no expansion. It then applies a
        fourth-order van der Corput estimate derived from S1.3.
      - The proof was checked by the lead and by a fresh-context referee: no FATAL or MAJOR finding
        (`review/2026-11-10-external-results-answers.md`).
      - The lemma still gives nondegenerate stationary phase in dimension n (`r = 0`) and the coupled lift I3b.
      - Hence the owner's revised order (above): A3 formalisation first, then I3a.
    - *Input derivative budget (2026-11-10).* A remainder `O(t^{−n/2−1})` cannot be controlled by C² amplitude bounds
      alone. For n = 2, an explicit family with uniform C² norm and zero leading term has integral exactly
      `π t^{−2} log(t/2)` (`review/2026-11-10-external-results-answers.md`, Result 2; check Q1). That family is a required
      bite datum. The statement must fix the input budget and distinguish four things: the input amplitude norm, the C²
      control of the reduced amplitude, a scalar remainder, and a remainder in a parameter-derivative norm.
    - *The hard part.* After elimination the reduced phase depends on `y` non-linearly. Every 2D bound it feeds must
      therefore be uniform over the resulting family of phases, not only over linear terms. S2.2F covers this for
      nondegenerate points only.
    - *Before the statement.* A prior-art sweep for existing formalisations. The relevant Mathlib names are not yet
      `#check`ed at the pin (lessons 1, 19). The mathematics is classical: stationary phase with parameters, Hörmander
      vol. I §7.7, cited from memory and not yet read. The claim can only be "machine-checked".
  - [ ] **I3b Dimension lift (acceptance test of the track; after I3a).**
    - *The theorem.* A Lean theorem for every `d ≥ 2`: at a point whose full Hessian has corank exactly 2 and whose
      third derivative, restricted to the Hessian's kernel, is a nondegenerate binary cubic, the integral decays like
      `t^{−2/3−(d−2)/2}` uniformly in the linear term. This is equivalent to "the transversely reduced phase is D4".
    - *Hypothesis on the reduced phase (2026-11-10).* A D4 restriction to a coordinate plane, together with nondegenerate
      remaining directions, is **not** enough. The external audit's phase `(z + x)²/2 + (x − 1/2)(x + 3y²)²` has both,
      yet its Hessian has corank 1 and it has a curve of critical points with decay `t^{−1}`, not `t^{−7/6}`
      (`review/2026-11-10-external-audit-answers.md`; `numerics/review/audit_checks.py` A1–A4). That phase is a required bite
      datum for the statement, and `(z + xy)²/2 + x³ − 3xy² + zx²` is a coupled positive control.
    - *Shape.* 5D and 6D come out as instances of `d`, not as new proofs. These are new statements on
      `EuclideanSpace ℝ (Fin d)`, with bridges to the frozen 2D statements, which are never edited.
    - *Optional early demonstration.* The fully separable corollaries: S4.1 times S1.2 in each extra direction, and the
      d-dimensional lattice kernel by T0E applied factor by factor (constant about `69^d`). They are described as
      Fubini corollaries, not as new capability.
      *Owner decision 2026-11-12:* the lattice-kernel corollary is promoted as batch HC (TdF, TdE′), with the T0E′
      constant `(8(1 + √7)/3)^d ≈ 9.72^d` instead of `69^d` (`docs/statements.md`, Batch HC).
    - *Not in scope.* Classification of singularities in d dimensions; critical manifolds (Morse–Bott) until a
      consumer needs them; infinite dimension.
- [ ] **I4 A "useful from" standard for every explicit constant.** Each explicit-constant statement in `docs/api.json`
      gets three fields: the parameter threshold above which it beats the trivial bound (T0E: `t > 518`; T6E:
      `t > 1321`, both from `docs/HANDOFF.md`), the best known bound for comparison with its citation (Landau's
      constant for T0E/T6E, `docs/prior_art.md`), and a checked numerical enclosure of the constant. A generator
      change (`tools/gen_api.py`, `docs/api/annotations.json`), checked by `make api-check`.
  - *2026-11-10/11:* batch LE2 (T0E′, T6E′; frozen, reviewed, proved in Lean at 48e7f24; replay in `docs/STATUS.md`) replaces the T0E/T6E thresholds 518 and
    1321 by 3.70 for both, with a constant within a factor 2 of the best (`docs/statements.md`, Batch LE2).
- [ ] **I5 Interface, frozen late.** One language-neutral contract (`docs/api.json` plus a certificate schema carrying
      exact constants and their enclosures) behind a CLI with JSON output, a Python package and a Rust crate. Version 1
      of the contract is frozen only after at least two consumers from different domains have used it; a C ABI and
      further languages come when a consumer asks. Trust boundary, fixed now: only the defined checker
      (`tools/oscint_check.py` or its successor) may give a result the status CERTIFIED; adapters transport and
      display evidence and can never confer that status.
- [ ] **I6 Credibility that adopters check first:** the human expert reading of the statements (owner item, §6; today
      every fidelity reading is by AI referees), a preprint, the Reservoir listing (§3), the first Mathlib pull request
      (§3).
- [ ] **I7 Fourier-grid certificate, proof of value (owner decision 2026-11-10; outside the core; after I1, I2 and the
      A3 work, never ahead of them).**
  - *Question.* Can OscInt deliver, for one matrix-valued periodic model, a guarantee that engineering software does
    not already give conveniently? The guarantee is a grid size N with a proved bound on the error of the sampled
    Fourier kernel.
  - *Mathematics.* Classical, from the external dossier (`review/2026-11-10-external-dossier-answers.md`, C5–C7, and
    its corrigendum):
    - analytic-symbol locality: Combes–Thomas by a contour shift, with `‖Im H(k + iθ)‖` bounded through the exact
      identity `‖b·σ‖ = |b|`;
    - the signed alias identity of the `−π` grid: `(−1)^{N(ℓ₁+ℓ₂)}` for odd N;
    - the alias bound.
  - *Deliverable.* One model (QWZ, any real m), in an optional package outside `OscInt/`. It contains:
    - a statement-first, reviewed and kernel-checked theorem;
    - an independently checked numerical enclosure of the error bound at stated (t, N, R);
    - a negative control: the unsigned identity, or the wrong parity, must fail.
  - *Stop rule, fixed now.* It enters the programme only if the same certificate is reused in a second, unrelated
    model or domain. Otherwise the record is kept and the work stops. No analytic-symbol API is frozen and no wrappers
    are built before that.
  - *Shared primitive (design note, not a claim).* On a translation-invariant lattice, conjugation by `e^{η·x}` has
    symbol `Ĥ(k + iη)`, so C5 and the graph bound D1 are one mechanism (`review/2026-11-10-external-dossier-answers.md`, follow-up round).
  - *Input from the external R3 packet (2026-11-13; `review/2026-11-13-external-R3-answers.md`).*
    - What it supplies: scalar statements of the alias identity and its budgets, exact parity controls by monomials, and
      a Poisson-kernel acceptance example. TRUE as hand mathematics; classical.
    - Its draft Lean elaborates only after three repairs. Its sanity layer has no parity control and would accept
      planted statement errors.
    - The continuum Poisson identity is already Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay`.
    - None of this is the matrix-valued deliverable. The gates and the stop rule above are unchanged.
- Input language for I1, I2 and I5: `docs/decisions/2026-11-09-input-language.md` (trigonometric polynomials with
  rational coefficients under an outer function `G` with `(G′)²` rational).

## Candidates (not commitments; owner decision 2026-11-10)
Proposals from reviews, chats and sessions that are not yet on this roadmap. A candidate is not a plan, and nothing
here is worked on. It moves to the roadmap only when it passes all four gates:
1. **Need.** It unblocks an item already on the roadmap, or the CENSUS ranking (I1) selects its theorem family, or a
   named consumer asks for it.
2. **Precision.** An informal statement with explicit hypotheses exists, and its checkable parts have been
   independently re-derived.
3. **Prior art.** A logged search has been run, and the novelty wording is fixed (usually "machine-checked").
4. **Owner decision,** recorded with its date in the item that replaces the row.

After I1's result, every row is re-ranked or dropped.

Promotions so far (for comparison):
- I3a passed gate 1 because S5.1′ needs it.
- I7 passed on the owner's decision and its engineering value alone. Its stop rule stands in for gate 1.

| Candidate | Source | Evidence so far | Waiting on |
|---|---|---|---|
| Reduced fourth-jet lemma `g'''' = Q − 3vᵀH⁻¹v` with r transverse variables | dossier A2 | re-derived for r = 2 (`numerics/review/dossier_checks.py` X2); classical splitting lemma | gate 1: the A3 route document (`docs/proof-A3.md`) decides whether S5.1′ uses it; else it folds into I3a |
| Gaussian and Schur lifts (exact reduction of Gaussian-structured higher-dimensional integrals to 2D) | dossier B1, B2 | identity checked (X8); classical | gate 1: subsumed by I3b's optional separable corollaries unless a consumer needs the Gaussian form |
| Weighted locality on finite block graphs, weak-link weights, truncation, Riesz projectors | dossier D1–D5 | bounds reproduced (F4–F6x); classical (Combes–Thomas) | gate 1: no roadmap item or consumer needs them; outside OscInt's subject (oscillatory-integral decay) |
| Explicit local constants: L6 (64(μν)^{−1/2}·W(A), 144μ^{−1/2}ν^{−1/3}·W(A)), L1 ((U₁/c + L₂U₀/c²)/m), and the exactly quadratic bound (Q) π√(‖A‖₂‖ΔA‖₂)/(m√\|det H\|), uniform in the linear term | external reviewer, R4 packet 2026-11-14, W2 (`review/2026-11-14-external-R4-answers.md`) | hand proofs checked by two fresh-context referees: TRUE, no BLOCKER or MAJOR; (Q)'s constant π is sharp; L6 is the repository's core argument with sharper bookkeeping, uniformly below `Core.lean`'s constant; checks `numerics/results-r4-packet-checks-2026-11-14.txt`; the general one-phase bound (G) is correct but useless at realistic parameters; (Q) is classical in kind (Hörmander Lemma 7.7.3) | gate 1 (a consumer; `docs/constants.md` §4.6 already names local L6/L1 as the cheap first deliverable) and gate 4 (owner); then a batch: the analytic Lean sanity layer the packet lacks, freeze, blind review |
| Composition of error certificates (`‖∏T − ∏T̃‖ ≤ Σ‖T_j − T̃_j‖` for contractions) | dossier E1 | elementary; not checked here | gate 1: I5's certificate schema, once two consumers exist |
| Finite-type fallback: on compact K ⊂ ℝ^d, if at every point some directional derivative of order 2…N has size ≥ δ, then the integral is ≤ C‖a‖_{C¹} t^{−1/N}, uniformly in the linear term | external audit §3/§4 | classical (Stein 1993, Ch. VIII §2, cited from memory); its 1D ingredient is S1.k, so it follows from S1.k with Fubini and a partition, with constants exponential in d | gate 1: would give a weak baseline bound for CENSUS models outside the catalogue; decided by I1's result; prior art to compare: Greenblatt, Rev. Mat. Iberoam. 41 (2025), uniform in linear perturbations (abstract read) |
| Newton-polyhedron (Varchenko-type) bounds built on the formalized Hironaka resolution (resolutionorg/hironaka v1.0.0, 2026-10-06; char 0, algebraic and real/complex-analytic; project claims no `sorry`, only the three standard axioms; not verified here) | external audit §4, memo §7 | existence of resolution is not an effective bound; the 2D route (Ikromov–Müller, Greenblatt) uses explicit Newton-polygon coordinates instead; Lean toolchain compatibility not checked | gates 1 and 3: only if I1 selects finite-type families beyond A3/D4; then a toolchain and axiom audit of the dependency |
| Matrix-valued propagators through gap closings (band crossings) | external audit §3 table, memo §6 F; external follow-up 2026-11-10 (QWZ at m = 2) | the vector-valued transfer (batch VT) assumes a fixed phase. Hand proofs for QWZ at the critical mass m = 2: a localized sup_x bound t^{−4/5}, sharp on eight rays with coefficient 𝒞 ≈ 9.934, and the next term t^{−4/3} on the rays where the bands cancel. Re-derived by a fresh-context checker (same model family as the lead) and checked by direct full-matrix quadrature (floating point; the sup over x only up to t = 8000); the uniform argument's constants and the support radius ρ₀ were not checked; constants existential (`review/2026-11-10-external-followup-answers.md`) | gate 1: no consumer or roadmap item needs it yet. Gate 2 met for QWZ m = 2 only, at the level of a hand proof re-derived by the same model family. Gate 4: owner decided 2026-11-10 not to freeze now |
| Small-data nonlinear lattice dynamics (discrete NLS): decay `(1 + t)^{−d/3}` of small solutions on ℤ^d whenever (d/3)(2p − 1) > 1 (d = 1: p ≥ 3; d = 2, 3: p ≥ 2; d ≥ 4: p ≥ 1), from the explicit ℓ¹ → ℓ^∞ bounds of T0E′/TdE′ ("bet 2", owner request 2026-11-12) | lead, session 10 | *Owner decision 2026-11-12:* its first step, the kernel-to-group identification (B1), is promoted as batch LS (`docs/statements.md`, Batch LS). External research packet 2026-11-12 (`review/2026-11-12-DNLS-packet-answers.md`): kernel-to-group identification (B1), global ℓ² well-posedness with mass and Duhamel (B2) and explicit small-data decay constants (B3), hand proofs checked by the lead; Lean statements in the packet do not elaborate; prior art Stefanov–Kevrekidis Theorem 3 covers the range qualitatively; earlier: scoping `docs/design/dnls-scoping.md`: a decay bootstrap needing no Strichartz estimate (Route 1); condition corrected 2026-11-12 after the HC adversarial review (`review/2026-11-12-HC-post-proof-answers.md`); only the kernel bound is machine-checked, the kernel-to-group identification is a planned lemma; prior art Stefanov–Kevrekidis 2005 (CITED-ABSTRACT); no Lean formalisation of Strichartz or a dispersive nonlinear PDE found | gate 1: a named consumer or owner decision; gate 2: re-derive Route 1 with explicit constants; then a route document for ℓ² well-posedness and the kernel-to-group identification (the go/no-go) |
| Explicit cube-root bound for the 1D discrete Klein–Gordon kernel: \|∫ e^{i(t√(m² + 2 − 2cos k) + ξk)} dk\| ≤ C* (a_m\|t\|)^{−1/3} for every m ≥ 0, a_m the maximum group velocity; uniform on m ∈ [0, m₀]; mass factor necessary | external reviewer, R2 packet 2026-11-12 (`review/2026-11-12-R2-KG-answers.md`) | hand proof re-derived by the lead (new parts) and a fresh-context referee: TRUE; the five envelopes are those of LE2, so the scalar half is already machine-checked for the cosine kernel; numerics `numerics/results-kg-checks-2026-11-12.txt`; rate and maximum velocity classical (Stefanov–Kevrekidis 2005 at mass 1, Egorova–Kopylova–Teschl 2015, read by the lead) | gate 1 (need: no consumer yet) and gate 4 (owner); then a batch: freeze, generalise the LE2 scalar layer, prove the KG level-set geometry, pieces and the limit m → 0 |
| Two-port memory consumer: an emitter coupled with opposite signs to sites ±1 of the cosine chain has memory kernel g²·2J₁(2Jt)/(2Jt) (one periodic integration by parts from `latticeKernel1 z 1`), hence the integrable envelope g² min{1, (C*/π)(2Jt)^{−4/3}} from T0E′, and a finite-horizon bound Q/(1 − Q) on the error of truncating the memory; with the same-sign, phase-error and zero-hopping controls | external reviewer, application-chains dossier 2026-11-13 (`review/2026-11-13-application-chains-answers.md`) | hand proofs checked by the lead and a fresh-context referee: TRUE; numerics `numerics/results-application-chains-checks-2026-11-13.txt`; the kernel is classical (Plyukhin–Schofield 2001 Eq. (60)) and the same-sign two-point kernel is in print (Zhang et al. 2023); the continuous truncation bound has a discrete analogue (Jørgensen–Pollock 2020 Eq. (22)) | gate 1 (a named consumer: an emitter or lead simulation with a declared tolerance) and gate 4 (owner); then a consumer example: the integration-by-parts identity and the envelope in Lean, the residual bound by hand or later |
| Imaging block consumer: in a normalised scalar SAR model (track (s, 0, 1), band ρ ∈ [1, 2], taper (1 − u²)³), off-diagonal blocks of radius 1/20 about (0, 2, 0) and (0, 1, 0) satisfy \|K_t\|/K_t(x, x) ≤ 336/(5√5) t^{−2} < 10^{−3} for t ≥ 174; mirror pairs and hard windows as controls | external reviewer, application-chains dossier 2026-11-13 (`review/2026-11-13-application-chains-answers.md`) | hand proof checked by the lead (exact constants by SymPy) and a fresh-context referee: TRUE; elementary (two integrations by parts in frequency), no novelty claimed | gate 1 and gate 4; then a consumer example from S1-type interval bounds |

## Standing: repository hygiene (owner directive 2026-11-10; lowest priority, ongoing)
Goal: reference-grade, consistent, current documentation and metadata, with drift caught by checks rather than by
people. Frozen and verbatim files are never edited (lessons 39; `review/` records): a finding in them is answered by
an allowlist, `REUSE.toml` or a new file. First audit: 2026-11-10, read-only, by a fresh agent. Its findings were
verified by the lead before any fix.
- [x] First pass (2026-11-10):
  - a dangling path in `docs/which-theorem.md`;
  - stale state in `docs/HANDOFF.md` and `docs/STATUS.md`;
  - `docs/downstream.md` pinned to v0.4.0;
  - the A3 row in the README status table;
  - a CHANGELOG "Unreleased" section;
  - code-span pipes escaped in the user-facing tables (15 rows).
- [x] Second pass (2026-11-10):
  - `tools/check_docs.py` (`make docs-check`, part of `make quick`) checks five things, each with a negative control
    in `--self-test`:
    - backticked repository paths exist, in the tree or in history; planned paths are in
      `tools/check_docs_allow.txt` with reasons;
    - Markdown table cell counts;
    - `docs/STATUS.md` agrees with `stamps/statements.json`;
    - every `rev = "v…"` pin in `docs/` matches the README;
    - privacy (lessons 46): no files under `review/prompts/`, and only answers and README directly in `review/`.
  - `make stamp-preflight` refuses a dirty tree before `make stamp` starts (lessons 25).
  - `docs/README.md`: a documentation index with a glossary of labels.
  - CONTRIBUTING: the verify-all duration (about two hours), and `codemeta.json` in the release bump list.
  - Lessons 25 and 26 closed (Cubic names in `MathlibNames.lean`).
  - `.zenodo.json`: `language`, and `related_identifiers` (isDerivedFrom roos-j/lean-oscillatory). The field names
    were checked against third-party copies of Zenodo's schema, not the official documentation; confirm at the next
    release deposit.
  - `codemeta.json`: `programmingLanguage`, `softwareRequirements`, `issueTracker`, `readme`, `relatedLink` and
    `developmentStatus`.
- [ ] **Still to do:**
  - a metadata check: version, title, keywords and concept DOI identical across `CITATION.cff`, `.zenodo.json`,
    `codemeta.json` and `lakefile.toml`;
  - a lessons-format check (entries 41–46 use a different heading form from 1–40);
  - link the glossary from the README's first screen;
  - the README Documents table completed against `docs/README.md`;
  - README wording: `numerics/` also holds exact checks that the records cite; `tools/` is not std-only Rust;
  - `docs/progress.md` entries for sessions 4–9 (CONTRIBUTING step 11);
  - the BibTeX suffix form and `version`;
  - whether a licence *list* in `CITATION.cff` / codemeta reads as OR (check the CFF 1.2.0 specification first).
- [ ] **Owner:**
  - Software Heritage archive and SWHID badge (open since v0.2.0, §3);
  - Reservoir listing;
  - CODEOWNERS and branch protection on `OscInt/Statements/`, `Challenge/`, `stamps/` and `review/`;
  - `SECURITY.md` for trust-chain bypass reports (lessons 22);
  - a pull-request template with the lessons-35/40 checklist;
  - an opt-in pre-push hook.

## 1. Finish and stabilise the mathematics
- [x] **S4.4** closed forms of c_C: machine-checked as stated (2026-11-07; `docs/STATUS.md`; verify-all PASS,
      `docs/replay/2026-11-06-S44-verify-all.txt`; post-proof FAITHFUL ×2; adversarial answered).
- [ ] Remove the duplication between `OscInt.D4.exists_piece_bound` and `d4BoundNe_of` (refactor the S4.1′
      assembly onto the lemma; the statement types are fixed, so the replay and type checks are the regression test).
- [x] Put `GammaFree.lean` into the next stamp: it is in `stamps/20261107T012459Z-2d5356432156` (RFC 3161 ×3) at its
      current SHA-256 `5dc19eb4…` (verified 2026-11-07, `docs/replay/2026-11-07-session4-baseline-quick.txt`).
- [ ] Commitment computation time (`make commit`, minutes): profile `oscint-commit-env` and make it incremental.

## 2. A usable public API
The frozen statements use audit-friendly encodings (`oscInt2` on `ℝ × ℝ` with the max norm, `AmpBound`, `FamilyCk`,
nested-`fderiv` `dd`/`ddd`). Users write Mathlib idioms. Each new statement below is frozen, stamped and reviewed
like the existing ones; front-end versions are proved from frozen statements by bridge lemmas, so they inherit the
trust chain.
- [ ] **Explicit or effective constants** for S2–S4 *(downstream, first priority; explored 2026-11-07,
      `docs/constants.md`: the existing route gives only crude constants)*: C as a computable function of
      the derivative bounds of the phase, the gradient lower bound, the amplitude bound and the support size. The
      downstream project found a gap of about 20 orders of magnitude between what an existential constant allowed it
      to prove and what was observed.
- [x] **Local smoothness hypotheses** *(downstream)* (front-end batch 3, 2026-11-08: FE-S2.1L/S2.2L/S3L/S4.1′L and single-phase
      forms, `docs/STATUS.md`, record `docs/replay/2026-11-08-session5-API3-verify-all.txt`; acceptance
      `examples/consumer/ConsumerLocal.lean`): every 2D statement now asks for a phase of class C⁴ on all of
      ℝ². Versions assuming smoothness only on a neighbourhood of the amplitude's support (natural for dispersion
      relations such as arccos-type phases, smooth only on an open set).
- [ ] **Parametric uniformity everywhere** *(downstream)* (done 2026-11-08 except S4: S2.2F family stationary phase,
      S3c fold with the classical hypothesis, family front ends; `docs/STATUS.md`; open: S4.1′ over a family): uniformity over compact families of phases for S2.2 and
      S4 (now only S3 and S2.1 have it), and a fold statement requiring the fold-or-nondegenerate condition only at
      critical points, as in the classical statement (S3 now requires it on all of K; its referee noted this).
- [ ] **Asymptotic expansions** *(downstream)*: the leading term of nondegenerate stationary phase,
      (2π/m)^{n/2} |det D²Ψ|^{-1/2} e^{iπ sgn/4} e^{imΨ(k₀)} A(k₀) + O(m^{-n/2-1}), and the Airy leading term for folds.
- [ ] **Front-end theorems** in Mathlib idioms (batch 1 done 2026-11-07: F1 `ContDiff`-plus-compact-support amplitudes,
      F2 the D4 limit with its closed-form constant, entry point `OscInt/API.lean`; batch 2 done 2026-11-07: S2.1, S2.2,
      S3, S4.1′ front ends for one phase, `docs/STATUS.md`; next: family versions,
      `iteratedFDeriv` conversions, `EuclideanSpace`) (integrals over `EuclideanSpace ℝ (Fin n)`, `ContDiff` plus
      `HasCompactSupport` amplitudes, norms via `iteratedFDeriv`).
- [x] **Conversion lemmas** *(downstream)*, front-end batch 2 (2026-11-07; C1–C9, C7′; `docs/STATUS.md`, record
      `docs/replay/2026-11-07-session4-final-verify-all.txt`), from standard formulations (a Hessian as a `Matrix`, rank and kernel
      conditions, the classical discriminant) to `FoldOrNondeg`, `hessDet`, `cubicCoeffs`, `GradLower`, `AmpBound`.
- [ ] **Hypothesis checkers** (lemmas done: `OscInt/Front/Poly.lean`, used by `examples/consumer/ConsumerFormula.lean`;
      tactic not started, needs a guard-policy decision): lemmas and a small tactic that discharge `disc (cubicCoeffs φ) ≠ 0`,
      `FoldOrNondeg`, `GradLower` and `AmpBound` for concrete polynomial phases and standard bumps, with failure
      messages naming the condition that fails rather than an unsolved goal.
- [ ] **Worked examples that double as non-vacuity checks** *(downstream)*: free Schrödinger decay, Bessel-function
      decay, an Airy-type fold, in `examples/` (planned).
- [x] **Sharpness lemma** *(downstream)* (SH `OscInt.API.sharpness`, batch GD; applied, with T6L, to the lattice kernel, `examples/consumer/ConsumerLattice.lean`; replay `docs/replay/2026-11-08-session6-GD-verify-all.txt`): a limit with a nonzero constant gives a matching lower bound on the decay
      rate (generalising the bite checks of S4.2 + S4.3).
- [ ] **Vector-valued amplitudes** *(downstream)* in a normed space (e.g. matrices), so spectral projections can be
      used directly instead of entry by entry.
- [ ] **Generality** *(downstream)*: dimension n for S2.1 and S2.2 (the largest audience gain); further singularity
      types — cusps (A₃, m^{-3/4}), D₅, E₆ — or, more ambitiously, the two-dimensional height / Newton-polygon bound
      of Ikromov–Müller, which covers these at once.

## 3. Interoperability and packaging
- [ ] **A stable way to depend on the library** *(downstream)*:
  - [x] a tagged release (`v0.2.0`, §6);
  - [x] a README section on adding OscInt as a Lake dependency, with a tested example project (`examples/consumer/`,
        built and checked locally; CI job `consumer` on main and pull requests); [ ] Reservoir listing (owner);
  - [x] a stated Mathlib upgrade policy (`docs/policy.md`; its cheap re-freeze path waits on the closure-diff tool below);
  - [x] a machine-readable list of statement names with their SHA-256 commitments, stamps and statement-file hashes
        (`stamps/statements.json`, generated and checked in verify-all), and a downstream checker
        (`tools/oscint_check.py`, hardened after the adversarial review of 2026-11-07; negative controls
        `tools/test_oscint_check.sh`). It detects drift, not tampering (README).
  - [ ] Closure-diff tool (technical debt from `docs/policy.md`): per-constant canonical hashes with local numbering
        and a listing of changed constants with old and new values, so a Mathlib upgrade can be re-frozen by one
        referee instead of a full new statement.
- [ ] **Mathlib version policy**: a documented bump procedure; a scheduled CI job building against a newer Mathlib
      that warns early. Statement commitments depend on Mathlib's definitions, so a bump changes them: decide (and
      record) the re-freeze rule, e.g. a machine-checked equivalence between each new statement and its stamped
      predecessor, then a new stamp and pin.
- [ ] Mathlib `module` syntax for the library files (needed to upstream; the statement files can only change with a
      re-freeze). Until then, `allowNonModules = true` in `lakefile.toml` (§4) would declare the mix.
- [x] Stable public names and a deprecation policy; semantic versions (`docs/policy.md`, from v0.3.0).
- [ ] **owner** Upstream the general lemmas listed in `docs/upstream.md` to Mathlib *(downstream: partitions of unity
      with compact support, the polar-coordinates integral and the uniform Leibniz bounds first)*.

## 4. Developer experience
- [x] Split CI (CI jobs `quick`, `verify`, `consumer`; `make quick`; `verify-all ONLY=`): a fast pull-request job (build, guard, axiom audit, type checks, `GammaFree.lean`) and the full
      replay (`verify-all`) on `main` and on a schedule; `make quick` for the local loop; `verify-all --only <step>`.
- [ ] Generated API documentation (doc-gen4) published as a site; a browsable blueprint site with the dependency
      graph built from `Blueprint/` and the route documents *(downstream)*; statement docstrings that cite the textbook
      statement they formalise *(downstream)*.
- [x] Build noise (seen in the CI log of PR #2; fixed in 828309a, 0 warnings): silence Lake's per-import module-system warnings with
      `allowNonModules = true` in `lakefile.toml` (Lake's documented opt-out; tested locally: 0 warnings, compilation
      unchanged); make `lean-replay`, `commit` and `comparator` depend on a `build/lean.ok` marker so `verify-all`
      runs the Lean step once instead of four times (lessons 7); replace the deprecated `if_false` in
      `OscInt/D4/LimitAssembly.lean`; install the pinned Rust toolchain explicitly in CI.
- [x] `CONTRIBUTING.md`: how to add a statement end to end (statement file, sanity theorems, challenge, comparator
      configuration, stamp, pins, blind review, blueprint, proofs, replay, post-proof review, STATUS row).
- [ ] A scaffolder (`tools` binary) that generates the statement file, challenge, comparator configuration, sanity
      stub and pin lines for a new statement.
- [ ] Actionable error messages from the Rust tools (what failed, which file, the command to reproduce, the likely
      fix).
- [ ] Mathlib's linters (docstrings, unused hypotheses, style) in CI.

## 5. Utility and integrations
- [ ] **owner** Choose the first application. Candidates (the brief's deferred list and downstream requests):
  - [ ] **periodic and lattice settings** *(downstream)*: integrals over the torus with periodic amplitudes (the
        kernels of discrete-time dispersive problems: lattice Schrödinger, discrete wave equations, quantum walks),
        and exponential-sum versions of van der Corput;
  - [ ] **from decay to Strichartz** *(downstream)*: an abstract Keel–Tao theorem for continuous and discrete time,
        with the Hardy–Littlewood–Sobolev input;
  - [ ] decay for lattice Schrödinger operators on ℤ²: done for the free discrete Laplacian (T6, T6L: kernel `O(t^{-2/3})` uniformly in `x` for `t ≥ 1`, sharp; ℓ¹ → ℓ^∞ for finitely supported data in `examples/consumer/ConsumerLattice.lean`; replay `docs/replay/2026-11-08-session6-GD-verify-all.txt`); with a potential: open.
- [ ] Numerics as a product: `numerics/` as a library and CLI with JSON output that checks hypotheses numerically,
      evaluates c_C and tabulates sharp rates for a given phase (tooling, never evidence).

## 6. Trust, provenance and release
- [ ] **owner** Human review of the statements: one expert reading `docs/statements.md` against
      `OscInt/Statements/` (today all fidelity readings are by AI referees).
- [ ] **owner** Mathlib built from source on a second machine (`lake build Mathlib` without the cache, then
      `make commit`), recorded in `docs/toolchain.md`.
- [ ] Upgrade the OpenTimestamps proofs in `stamps/` from pending to Bitcoin-attested, and verify them.
- [ ] **owner** Branch protection on `main` requiring CI (checks named in `docs/decisions/2026-11-08-ci-release-review.md` §4). [x] Dependabot for the SHA-pinned GitHub Actions (`.github/dependabot.yml`, session 6).
- [ ] **First release** (`v0.2.0`; steps 1–4 done, step 5 open), in this order:
  1. [x] author name and ORCID iD in `CITATION.cff` and `.zenodo.json`; ORCID badge in `README.md`;
  2. [x] **owner** repository connected to Zenodo and ORCID (2026-11-06);
  3. [x] **owner** GitHub release `v0.2.0` published (2026-11-06); Zenodo minted 10.5281/zenodo.24021329
     (concept DOI 10.5281/zenodo.24021328);
  4. [x] Zenodo DOI badge in `README.md`; `doi:` and `identifiers:` in `CITATION.cff`;
  5. archive in Software Heritage (owner, "Save code now"); [ ] sign release artifacts (Sigstore build-provenance attestation prepared in `release-candidate.yml`, session 6; not ticked until its first run).
- [x] **owner** Release v0.3.0: published 2026-11-07 (tag → 7098f09; external dry run
      `docs/replay/2026-11-08-external-downstream-dry-run-v0.3.0.txt`); prepared 2026-11-07 (`docs/release-notes/v0.3.0.md`, CHANGELOG, version 0.3.0 in
      `lakefile.toml`, `CITATION.cff`, `.zenodo.json`); CI job `release-pin` is red until the tag exists.
- [ ] **owner** Publication: venue, preprint, outreach.
