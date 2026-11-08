c98f4962f9fbf7d8158fc5b4acbb15d965885488

# Adversarial review: batch GD, API index tooling, session-6 records, licensing (f) and citation metadata (g)

Referee: fresh context, hostile. Prompt: `review/prompts/GD-adversarial.md`, plus claims (f) and (g) from the lead.
`git rev-parse HEAD` = c98f496 (unchanged during the review). All checks ran on a clean clone at c98f496 in
`/tmp/advGD/clone`. Lean ran with the repository's oleans (`LEAN_PATH` from `lake env printenv LEAN_PATH`, then plain
`nice -n 10 lean`): no `lake build`, no `make`, nothing written to the repository. Observation: the working tree of
`/home/user/lean-oscillatory` has uncommitted edits to `.github/actions/setup-lean/action.yml` and
`.github/workflows/verify.yml` that are not mine and not in c98f496. I reviewed the committed versions. One of my Lean
runs overlapped another process's `lean Axioms.lean` (pid 2028, not mine).

## Verdict

- **No BLOCKER and no MAJOR.**
- **(a) holds.** The order part is supported by the timestamps, but nothing in the repository records when the proof
  work started.
- **(b) holds as recorded.** I reproduced two plants exactly. The structural claim in the sanity file is overstated:
  two plausible plants that weaken T1's conclusion are not detected. One rejection I planted came from proof-term
  brittleness, not from the statement being false.
- **(c) holds for drift between the inputs and the generated outputs.** The hand-written annotations are checked
  against nothing, and the snippet check is a substring test.
- **(d) holds, with smaller scope than the prose.** The data must be finitely supported and t ≥ 1. The compiled
  sharpness covers only exponent 3/4. The propagator is a definition and is not checked.
- **(e) is mostly accurate.** The release notes assume a docs-only step-5 outcome, and one fact in the memo is stale.
- **(f) holds.** `reuse lint` reports compliant (520/520 at c98f496). Licensing is accurate except that AI
  authorship is not disclosed.
- **(g) is accurate on names, ORCID and DOIs.** The version-0.3.0 metadata already describes v0.4.0 content, and
  `codemeta.json` is outside the release preflight.

## What I verified (no finding)

- **Stamp manifests.** Every file line in `stamps/20261108T094842Z-edf7787a2845/manifest.txt` and
  `stamps/20261108T102629Z-8c8d7b090adb/manifest.txt` equals `git show <commit>:<path>` for commits edf7787 and
  8c8d7b0. Neither manifest leaves out a file of its commit (script `/tmp/advGD/chk.sh`). The 8c8d7b0 manifest
  contains no GD proof file (GlobalLocal, Torus, LatticeSymbol, LatticeKernel, GlobalAssembly, Sharpness,
  LatticeLimit). The only statement-like files in it are the statement-only drafts `docs/design/torus-lattice/TorusDraft.lean.txt`.
- **Timestamp tokens.** All three RFC 3161 tokens of each stamp carry the SHA-256 of that stamp's manifest. Their
  genTime is 09:48:45Z and 10:26:32Z. For the review stamp, `openssl ts -verify` against the pinned roots gives
  Verification: OK for DigiCert, Sectigo and FreeTSA.
- **Commit order.** `git log`: statements edf7787 09:38, pins b71615c 09:56, reviews 8c8d7b0 10:17, review stamp
  ff79840 10:26:43, first proofs 2aae8dd 10:36:22, T6L c62a621 10:44:21. `git diff edf7787 HEAD -- OscInt/Statements Challenge`
  is empty. The `file_sha256` of Global.lean in `stamps/statements.json` (edaaf9c6…) equals the stamped hash.
- **Proofs and axioms.** `/tmp/advGD/lean/Ax.lean` compiles. It contains `example : XStatement := OscInt.API.x` for
  all eight. `#print axioms` on globalDecayCrit, globalDecay, torusUnfold, latticeLaplacianDecay and
  latticeLaplacianLimit gives only [propext, Classical.choice, Quot.sound]. `StatementTypes.lean` asserts all eight
  types, and `comparator-GD.json` names all eight.
- **Fidelity of the statements.**
  - The integrand is continuous on all of ℝ² and compactly supported. A is 0 off `tsupport A ⊆ K ⊆ U`, so each point
    outside U has a neighbourhood on which A vanishes. The "Bochner integral of a non-integrable function is 0" junk
    case cannot occur.
  - `iteratedFDeriv` is evaluated only at points of K ⊆ U or D ⊆ U, with U open, so there are no junk derivatives.
  - `m ^ σ` appears only with m ≥ 1 or under `atTop`.
  - Quantifier order is right: C depends only on (Ψ, K, U, D) or (…, K′) and is uniform in A, M, L, m.
  - The max norm changes only constants, and T1's ball is the square [−4, 4]², as its docstring says.
  - `IsD4Point` uses `Cubic.discr` with the binary-cubic discriminant formula, so a = 0 is handled.
- **Lattice kernel and T6L.**
  - The kernel is the e^{itΔ} kernel up to the documented changes: the factor (2π)^{-2}, the phase e^{-4it} and t ↦ 2t.
  - The phase at x = (n, n) has exactly one critical point in the box, (π/2, π/2). Its value there is nπ, which gives
    the factor (−1)ⁿ, and its cubic part there is (κ₁³ + κ₂³)/6.
  - The constant agrees: Γ(1/3)² 6^{2/3}/3 = Γ(1/3)² 48^{1/6}/√3 ≈ 1.1006 Γ(1/3)².
- **Consumer propagator.**
  - With f̂(k) = Σ f(x) e^{-ix·k}, the solution operator e^{-itH} of i∂ₜu = Hu, where Ĥ = −(cos k₁ + cos k₂), is
    exactly `(2π)^{-2} Σ_y K(t, x − y) f(y)`.
  - H = −(Δ + 4)/2, and e^{itΔ} = e^{-4it} e^{-i(2t)H}. So "up to a constant and a time scale" is correct.
- **API generator.**
  - `python3 -I tools/gen_api.py --check .` reports ok on the clone, and `tools/test_gen_api.sh` reports PASS (6/6).
  - `lean_statement` is read from the working-tree statement file. `statements check` (part of `make quick`) fails
    whenever that file no longer has its pinned hash. In effect the text is the stamped one.
- **Release-note pins.** sha256 of `stamps/statements.json` = 183b045a…, and of `tools/oscint_check.py` = f5b6bb77….
  Both match `docs/release-notes/v0.4.0.md`. `tools/release_preflight.sh 0.4.0` fails only on the version bump and
  the CHANGELOG heading, as stated.
- **Licensing.**
  - `reuse lint` (reuse 6.3.0) at c98f496: compliant, 520/520. `cffconvert --validate`: valid.
  - `actionlint` at c98f496: no output.
  - `LICENSES/Apache-2.0.txt` equals `LICENSE` up to whitespace.
  - The derived S1 files keep upstream's exact line "Copyright (c) 2025 Joris Roos. All rights reserved." and its
    "Authors: Joris Roos, Manasa Praveen". I checked this against
    `raw.githubusercontent.com/roos-j/lean-oscillatory/cf564e0…/LeanOscillatory/VanDerCorput.lean`. They add a
    modification notice (Apache-2.0 §4(b)).
  - `reuse spdx` gives `OscInt/Statements/VanDerCorput.lean` both copyrights (Roos 2025, Falk 2026).
  - `Challenge/VanDerCorput.lean` only references the statement constants, so Falk-only is right there.
  - The header record's challenge-export hashes equal the `*.ndjson` lines of the pinned stamp manifests.
  - Every Lean source file of the trust chain (`OscInt/Statements/*.lean`, `Challenge/*.lean`) is unchanged since its
    stamp. The headers touched only other files.
- **Citation metadata (g).**
  - ORCID public API for 0009-0001-9478-6061: given-names "Thomas", family-name "Falk III", public email
    research@thomas-falk-research.com. CITATION.cff, codemeta.json and .zenodo.json ("Falk III, Thomas") match.
  - Zenodo API: 24045231 is version 0.3.0 (2026-11-07) and 24021329 is version 0.2.0 (2026-11-06). Both have concept
    DOI 10.5281/zenodo.24021328, which resolves (302 to zenodo.org).
  - References: Mathlib CPP 2020, pp. 367–381, doi 10.1145/3372885.3373824; Lean 4 CADE-28, pp. 625–635,
    doi 10.1007/978-3-030-79876-5_37; Stein 1993, PMS 43, ISBN 0-691-03216-5.
  - The MSC2020 codes and their titles (42B20, 41A60, 35Q41, 68V20, 03B35) are right.

## Findings

### (a) Order and freezing

**MINOR a1. The order claim rests on the lead's word, and the review stamp is never machine-verified again.**
`stamps/pins.txt` pins only statement stamps, so `make stamp-verify` and verify-all ("all pinned stamps verified")
never check `stamps/20261108T102629Z-8c8d7b090adb` (or the API3 review stamp `…010546Z-7bb457958327`).
- **Failure scenario.** A corrupted or replaced review stamp would pass every CI and replay check. A timestamp can
  show that the reviews existed by 10:26:32Z; it cannot show that no proof existed before then.
- **Evidence on timing.** The only evidence is outside the repository: agent scratch directories on this machine.
  - `/tmp/gdp2/names.lean` 10:27:57, `/tmp/gdp1/c.lean` 10:28:33, `/tmp/gdp2/TorusAx.lean` 10:29:22,
    `/tmp/gdp3/LatticeSymbolAx.lean` 10:30:09, `/tmp/gdp4/LatticeLimitAx.lean` 10:36:07.
  - These are consistent with work starting after the stamp.
  - They also mean a complete 176-line T1 proof with `#print axioms` was compiled 85 s after that agent's first
    Mathlib-name check, and 2 min 50 s after the stamp.
  - The repository keeps none of this.
- **Fix.**
  - Have `stamp verify-pinned` also verify every stamp directory, or pin review stamps under a `review:` key.
  - Commit the proof agents' launch times (or transcript headers) with the proof commit.
  - Word the claim as "reviews stamped before the first proof commit (10:36:22Z); agent launch times in <file>".

### (b) Sanity theorems and plants

I regenerated plants with the record's own generator (`plants_gd.py.txt`, run with plain `lean`; my copy is
`/tmp/advGD/scripts/plants.py`, output in `/tmp/advGD/out`).

**Reproduced.** GD-drop-kD (ok accepted; plant rejected, first error `19:3 Application type mismatch`) and T1-period
(ok accepted; plant rejected, `26:4 Type mismatch: After simplification`). Line and column are identical to the record.

**MINOR b1. Two conclusion-weakening plants of T1 are not detected, against the file's structural claim.**
`OscInt/Front/GlobalSanity.lean:16–18` says a sanity theorem "detects a plant that makes a hypothesis harder to
discharge or the conclusion weaker". `torusUnfold_moments` (`GlobalSanity.lean:423ff`) throws away two of T1's three
conclusion conjuncts (`obtain ⟨η, -, -, hη⟩ := h`). So:
- `X-T1-support`: `tsupport η ⊆ Metric.closedBall 0 4` ↦ `… closedBall 0 400` is **accepted**.
- `X-T1-smooth`: `ContDiff ℝ ∞ η` ↦ `Continuous η` is **accepted**.
- Both are recorded in `/tmp/advGD/out/plant-X-T1-*.out` (empty output, exit 0).
- **Failure scenario.** Before the proof, a T1 text with a useless weight (merely continuous, or with huge support)
  would have passed the sanity layer. That weight is exactly what R8/R9 needs to be smooth and supported in the
  square.
- **Impact.** None on the proved statement, which was reviewed FAITHFUL ×2. The claimed detection class is wider
  than what is tested.
- **Fix.** Restate the conclusion: `∃ η, ContDiff ℝ ∞ η ∧ tsupport η ⊆ closedBall 0 4 ∧ ∫ η = (2π)² ∧ ∫ η e^{ik₁} = 0`,
  add the two plants, and record them.

**MINOR b2. A rejection is not a semantic detection, and the "smooth only on U" branch has no datum.**
- `X-GD-C5`: `ContDiffOn ℝ 4 Ψ U` ↦ `ContDiffOn ℝ 5 Ψ U` in GD is **rejected**
  (`plant-X-GD-C5.lean:22:4 Application type mismatch … ContDiffOn ℝ 4 (genCubic 1 0 0 1)`).
  - The datum x³ + y³ is C^∞, so the planted statement is still dischargeable on it.
  - The rejection comes from the proof term `genCubic_contDiff` being stated at order 4, not from the mutation being
    false on the data.
  - In this case brittleness, not falsity, explains a "rejected".
- `X-GDN-global`: `ContDiffOn ℝ 4 Ψ U` ↦ `ContDiffOn ℝ 4 Ψ Set.univ` in GD-N is **accepted**. It is a plausible plant
  (it drops the local-smoothness modelling choice) and makes a hypothesis harder to discharge, yet it is missed.
- Every GD datum is a global polynomial. Lessons 38 ("at least one datum in each branch") is not applied to the
  modelling choice "smoothness: C⁴ on U only" (annotations; `Global.lean` docstring).
- The arccos family of `examples/consumer/ConsumerLocal.lean` is a natural datum that is smooth only on a region.
- **Fix.**
  - Add one GD-N or GD-F datum smooth only on U (e.g. `Real.sqrt (1 - ‖k‖²)` on the unit ball, or an arccos phase).
  - In the plant record, for each plant state whether falsity on the data is proved (as `fold_det_zero`,
    `hypShift_hessian_zero_ne` and `zero_not_mem_offK` do) or only a term mismatch.
  - Five of the 15 recorded plants have such a falsity proof in the file. For the others the rejection is a
    type-level mismatch against a restated conclusion.

### (c) API index

**MINOR c1. The hand-written annotations are checked against nothing, and the snippet check is a substring test.**
`tools/gen_api.py:61–66` tests `short not in snip`. In a scratch copy (`/tmp/advGD/apit`) I set GD's annotation to:
- `snippet: example : GlobalDecayCritStatement := OscInt.API.globalDecayCrit` ("globalDecay" is a substring);
- `rate: m^{-1}`;
- `hypotheses: ["none"]`.

`gen_api.py` regenerates and `--check` prints "api: ok". The snippet would also compile, so `make quick` stays green.
- **Failure scenario.** An agent reading `docs/api.json` takes GD's rate or hypotheses from a wrong annotation.
- **Real instance of the gap.** GD-F and GD-N annotations omit "K compact".
- **Docstring mismatch.** The module docstring claims "an unproved statement's snippet names its statement constant
  and not a theorem"; the code checks only the first half.
- **Fix.**
  - Match whole identifiers (`re.search(r'(?<![\w.])' + re.escape(proved_by) + r'(?![\w])', snip)`).
  - Require each snippet's `example` type to be the label's own constant.
  - Derive `rate` from the Lean text where it is a literal `m ^ (-(p : ℝ) / q)` or `/ m`.
  - Add these as plants in `tools/test_gen_api.sh`.

**NIT c2.** `lean_text` stops at the first blank line and omits the docstring. That is harmless today; say so in
`docs/api/annotations.json` conventions.

### (d) Consumer example

**MINOR d1. The compiled sharpness is weaker than the prose.**
- `examples/consumer/ConsumerLattice.lean:15` says "shows that no better power holds", and claim (d) says "sharp".
- `not_faster` (`:48`) and `latticeLaplacian_sharp` exclude only `t^{-3/4}`.
- The general statement follows in about 15 lines from the same two theorems. `/tmp/advGD/lean/Ax.lean`
  `not_faster_all : ∀ σ' > 2/3, ¬ ∃ C, ∀ t x, 1 ≤ t → ‖latticeKernel t x‖ ≤ C * t ^ (-σ')` compiles.
- **Fix.** Replace `not_faster` with the ∀ σ′ > 2/3 form. Optionally also expose SH's lower bound
  `|K(n,(n,n))| ≥ (c/2) n^{-2/3}` eventually.

**MINOR d2. "Propagator" is a definition, and the ℓ¹ claim is narrower than its wording.**
- `propagator` (`ConsumerLattice.lean:27`) is the kernel formula. No Lean statement ties it to i∂ₜu = Hu, and
  `propagator 0 f = f` is not proved either. The t = 0 sanity values in GlobalSanity cover only x = 0 and x = (1, 0).
- `dispersive` is for `f : ℤ × ℤ →₀ ℂ` (finitely supported) and t ≥ 1. It says nothing for ℓ¹ data, for t ∈ (0, 1)
  (trivial with C ≥ 4π²) or for t < 0 (by conjugation).
- **Fix.**
  - Say "on finitely supported data, t ≥ 1" in the docstring, CHANGELOG:24, HANDOFF:12 and ROADMAP:114.
  - Add `propagator 0 f = f`. It needs `latticeKernel 0 x = (2π)² · [x = 0]`, which is the general form of
    `latticeKernel_zero_one`.

### (e) Memo and release notes

**MINOR e1. The release notes assume a docs-only step-5 outcome.**
- `docs/release-notes/v0.4.0.md`, "Publishing (owner), after the step-5 decision", step 1, says "Apply the step-5
  decision (docs only, memo §4)".
- Option (ii) of the memo is not docs-only. It re-freezes API3 as API3′ with ten new statements, so
  `stamps/statements.json` and both pins change, and the memo itself says "v0.4.0 waits for it".
- The process note ("the owner's decision on it is recorded in docs/STATUS.md") states a future fact as present.
- **Fix.** "Apply the step-5 decision. Under (i) or (iii) it is docs only and the pins stay valid; under (ii) this
  release is re-prepared after API3′."

**NIT e2. A fact in the memo is now stale.**
`docs/decisions/2026-11-08-step5-memo.md` §2 says "`git diff 9d03130 HEAD -- OscInt/Statements Challenge` is empty".
At HEAD it shows `Global.lean` and `Challenge/Global.lean` (+176). The claim is true only for the API3 files. Fix:
scope the command to `OscInt/Statements/Family.lean Challenge/Family.lean`.

**OK.** The memo and HANDOFF leave all decisions to the owner. The ten "owner decision pending" STATUS rows exist
(count 10).

### (f) Licensing

**MINOR f1. Authorship is not disclosed.**
- The headers say "Authors: Thomas Falk III" and claim "Copyright (c) 2026 Thomas Falk III. All rights reserved."
  for files the commits attribute to AI proof agents and the lead agent: commit author "Claude
  <noreply@anthropic.com>"; 2aae8dd says "by proof agents". Example: `OscInt/Front/Torus.lean` (agent GD-P2).
- CITATION.cff and README do not mention AI authorship of the code. README:127 discloses only AI referees.
- The project already discloses AI review, so this is an accuracy question, not compliance. Whether the copyright
  line is right is the owner's question, not the referee's.
- **Fix (owner's choice of wording).** Add an AI-assistance statement to README and CITATION.cff (`abstract` or a
  `notes`-style sentence), and optionally `SPDX-FileContributor` lines.

**NIT f2. The file counts disagree.**
- The commit message for 1cc4921 and the session-6 checklist (REUSE item) say "517/517".
- The record (`docs/replay/2026-11-08-session6-licence-headers-checks.txt`, item 4) says "518 / 518".
- At c98f496 `reuse lint` gives 520/520.
- Fix: cite the count with its commit.

**NIT f3. The headers record does not cover every trust-chain step.**
- It covers the exports, `make commit` and `make quick`.
- It does not record leanchecker or export-kernel replays on the headed tree, and the only verify-all is on
  c62a621.
- Kernel replay is insensitive to comment shifts, and release-candidate will replay. State this scope.

**NIT f4.** `stamp verify` writes `.blob` inside the stamp directory (`tools/src/bin/stamp.rs:156`). An interrupted
run leaves an untracked file under `stamps/*/`, and the directory mtime changed at 12:31. Use a temp directory.

**NIT f5.** In CI, `pip install reuse==6.3.0 cffconvert==2.0.0` (`.github/workflows/ci.yml:61`) is version-pinned
but not hash-pinned. Use `--require-hashes` with a lock file, as for the toolchain.

### (g) Citation metadata

**MINOR g1. Version 0.3.0 metadata describes v0.4.0 content, and codemeta.json is not checked.**
- CITATION.cff, .zenodo.json and codemeta.json at HEAD all say version 0.3.0, released or published 2026-11-07.
  Their abstract and description already list global decay, the lattice-Laplacian estimate and sharpness, which are
  not in v0.3.0.
- GitHub's "Cite this repository" on `main` therefore attributes the GD results to v0.3.0 (DOI 24045231).
- `tools/release_preflight.sh` checks the version in lakefile, CITATION.cff and .zenodo.json. It does not check
  codemeta.json `version` or `datePublished`, CITATION `date-released`, or the version-DOI list. The v0.4.0 notes'
  step 1 omits codemeta.json.
- **Fix.**
  - Keep the abstract at what the declared version contains, or bump everything together at release.
  - Add codemeta `version`/`datePublished` and CITATION `date-released` to the preflight, with a plant each.

**NIT g2.** The Lean 4 reference has `collection-title: "Lecture Notes in Computer Science"`. Its proceedings are
"Automated Deduction – CADE 28" (LNCS 12699). Put the proceedings in `collection-title` and add `volume: 12699`.

**NIT g3.** HANDOFF item 4 lists "the Zenodo DOI of v0.3.0 in CITATION.cff" as open; it is already there
(24045231). README's header line gives the concept and v0.2.0 DOIs but not v0.3.0 (it appears only under How to cite).

### Prose (README, STATUS, CHANGELOG, ROADMAP, HANDOFF, checklist, which-theorem, applications)

**MINOR p1. `docs/applications.md:8–11` understates.** T6/T6L still say "statements frozen and reviewed …; see
`docs/STATUS.md` for whether they exist yet". Both are proved, and `examples/consumer/ConsumerLattice.lean` is
compiled in `make quick` (Makefile:85). Fix: mark it **demonstrated** (`ConsumerLattice.lean`, `dispersive`,
`not_faster`) with the d2 scope.

**MINOR p2. `docs/ROADMAP.md:114` overclaims.** It ticks "decay for lattice Schrödinger operators on ℤ²". Only the
free discrete Laplacian is covered: no potential, and the data must be finitely supported. Fix: "for the free 2D
lattice Schrödinger group (discrete Laplacian)".

**NIT p3.** README's opening paragraph lists S1–S4 and front ends, but not batch 3 or GD.

**Checked, no issue.**
- STATUS rows GD-C…T6L: proved, replayed, post-proof pending. They match `docs/replay/2026-11-08-session6-GD-verify-all.txt`.
- CHANGELOG batch GD (15 plants before any proof) matches the plant record and the commit order.
- `docs/which-theorem.md` rows match the statement texts.
- In `docs/applications.md`, every other "demonstrated" points at a file in `make quick`: `ConsumerLocal.lean`
  (arccos FE-S2.1L, `foldOn`, `foldCrit_fold_bite`) and `ConsumerFormula.lean`.

## Answers to the attack list

| Attack | Result |
|---|---|
| Junk integral | Cannot occur (the integrand is continuous and compactly supported). |
| Junk `fderiv` / `iteratedFDeriv` | Only taken on U open. |
| `m ^ σ` with m ≤ 0 | Excluded. |
| Quantifier order | Right. |
| Max norm | Constants only; T1's square is documented. |
| Order claim | Stamps and manifests verify; the review stamp is unpinned (a1). |
| Plant generator | 2/15 reproduced; brittleness instance (b2); missed plants (b1, b2). |
| API generator and self-test | Drift fails as claimed; annotation and substring gaps (c1). |
| Consumer propagator | The correct kernel of the stated equation, as a definition only (d2). |
| Prose | p1, p2, p3. |

## Files

- Report: `/tmp/claude-0/-home-user-lean-oscillatory/09e4b675-9e8c-501f-90e3-32d7c8e65b8e/scratchpad/GD-adversarial.md`
- Plant runner: `/tmp/advGD/scripts/plants.py`; outputs: `/tmp/advGD/out/{ok,plant}-*.{lean,out}`
- Axioms and generalized sharpness: `/tmp/advGD/lean/Ax.lean`
- API substring demonstration: `/tmp/advGD/apit/`
- Manifest checker: `/tmp/advGD/chk.sh`
