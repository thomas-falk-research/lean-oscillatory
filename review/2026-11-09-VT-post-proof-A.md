09e4bc72c1a931cb5563e70b22f403373cb00d92

# Post-proof referee A: batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

**Summary.** All four theorems are FAITHFUL at full scope, with no BLOCKER and no MAJOR findings. Each theorem's type is exactly its frozen constant. The frozen file matches its stamp byte for byte. The proofs use only the four proved scalar GD theorems, the duality part, and Mathlib. Every recorded order point matches what is on disk; one claim (the route review came before the proof) rests only on evidence the lead controls. Findings: 2 MINOR, 4 NIT. I wrote nothing in the repository (`git status --porcelain` is empty). My scratch files are in /tmp/vtpostA/ (check1.lean, nonvac.lean, matrix.lean). I ran one Lean process at a time under `nice -n 10` and did not run `make` or `lake build`.

## (1) Type is exactly the frozen constant
- **SHA-256 of the frozen file.** `OscInt/Statements/Vector.lean` hashes to `784ca9a5…c2ba` at HEAD. That is the entry in `stamps/20261108T235416Z-961cebc296ef/manifest.txt` and the `file_sha256` in `stamps/statements.json`.
  - The same holds for every other `OscInt/Statements/*.lean`, `Challenge.lean`, `Challenge/*.lean`, `comparator-VT.json`, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`. All are unchanged since the stamp.
  - The only change to `StatementTypes.lean` is the four new `#assert_type_is` lines (lines 76–79).
- **Text comparison.** A script compares each vector statement with its scalar one in `OscInt/Statements/Global.lean`. After replacing `∀ (A : ℝ × ℝ → ℂ)` by the E binder plus `(A : ℝ × ℝ → E)`, and `*` by `•`, the texts are identical for all four.
- **TYPE-OK.** The replay has the four TYPE-OK lines (`docs/replay/2026-11-09-session7-VT-verify-all.txt`, lines 126–129). My own syntactic check (`Expr` equality against `mkConst`, in /tmp/vtpostA/check1.lean) passes for all four. Each is a `thmInfo`.
- **Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all four and for `OscInt.VectorAux.transfer`.
- **Comparator.** `comparator-VT.json` lists the four names with permitted axioms only. The replay (line 638) shows "comparator-VT.json accepted against stamps/20261108T235416Z-961cebc296ef", with all six kernels. The challenge export hash `28f04e54…` matches the stamped manifest.

## (2) Verdicts
| Theorem | Verdict | Scope |
|---|---|---|
| `OscInt.API.globalDecayCritVec` (GD-C-V) | FAITHFUL | full |
| `OscInt.API.globalDecayVec` (GD-V) | FAITHFUL | full |
| `OscInt.API.globalFoldVec` (GD-F-V) | FAITHFUL | full |
| `OscInt.API.globalNondegVec` (GD-N-V) | FAITHFUL | full |

How each statement matches the docs:
- Hypotheses on Ψ, K, U, D and K′ are the scalar ones, and so are the rates m^{−2/3}, m^{−2/3}, m^{−5/6} and m^{−1}.
- `∃ C` is placed after the phase data and before `∀ E`, as the docs say.
- E ranges over complex Banach spaces in `Type`. The integral is Bochner's with the scalar action. `ContDiff ℝ 2` and `iteratedFDeriv ℝ` use `complexToReal`.
- Limitations stated in the docs, not defects: universe 0 only; real Banach spaces not covered (clarifications 1, 3, 7).
- Clarification 5 holds: E = ℂ gives the scalar statements (`VectorSanity.*_of_vec`), and duality gives the converse with the same constant.

## (3) Non-vacuity on compiled data
- **Sanity file.** `OscInt/Front/VectorSanity.lean` instantiates all four statements on concrete phases: quadPhase (GD-N-V), foldPhase (GD-F-V), ellPhase with D = {0} (GD-V), and ellPhase with K′ = {0, L₁} (GD-C-V). The spaces are `Fin 2 → Fin 2 → ℂ`, `ℂ × ℂ`, `ℕ →ᵇ ℂ` (infinite-dimensional), and the family `EuclideanSpace ℂ (Fin n)` for every n with one C. `examples/consumer/ConsumerVector.lean` applies these to the proved theorems.
- **Gap.** These sanity theorems never build an actual nonzero amplitude. So I compiled one myself (/tmp/vtpostA/nonvac.lean, all axioms standard):
  - A = (ContDiffBump at 0, radii 1/4 and 1/2) • v, with `A 0 = v ≠ 0`;
  - proofs of `ContDiff ℝ 2 A`, `tsupport A ⊆ closedBall 0 1` and a finite M bounding the derivatives for j ≤ 2;
  - the theorem applied to it: GD-N-V on `ℕ →ᵇ ℂ` (v = const 1), and GD-C-V (with L₁), GD-V and GD-F-V on `ℂ × ℂ`.
- **E-uniform constant on operator-valued amplitudes.** One C for all n with E = `(Fin n → ℂ) →L[ℂ] (Fin n → ℂ)` compiles. The user's native ℝ-structure instances are accepted against the statement's `complexToReal` by defeq.
- **Matrices and universes.** `Matrix (Fin n) (Fin n) ℂ` with the local `linftyOp` instances (clarification 6) and the polymorphic `transfer` at `E : Type 1` both elaborate (/tmp/vtpostA/matrix.lean).

## (4) Dependencies
- **Direct OscInt constants used, checked by a meta command (check1.lean):**
  - `globalNondegVec` uses `gdnv_of` and `vecTransfer`.
  - Each `gd*_of` uses only the statement definitions, `VecTransferFacts`, `theta_cont`, and one scalar theorem: `OscInt.API.globalDecayCrit`, `globalDecay`, `globalFold` or `globalNondeg` respectively.
  - `vecTransfer` uses `transfer`, which uses `integrand_continuous`. That one, and `theta_cont`, use no OscInt constant.
- **Transitive walk.** Stopping at API theorems, the walk from each vector theorem reaches exactly one other `OscInt.API` constant: its scalar counterpart. Those counterparts are proved and TYPE-OK at HEAD.
- **Conclusion.** The proofs rest only on the proved scalar GD statements and Mathlib, with standard axioms.
- **The proof itself.** `VectorParts.lean` follows the reviewed route: Hahn–Banach, `integral_comp_comm` on a continuous, compactly supported integrand, then `norm_iteratedFDeriv_comp_left` on `g.restrictScalars ℝ`. The assembly passes the scalar C before E.

## (5) Order and other claims against the evidence
**Commit order:**

| Time (UTC) | Event |
|---|---|
| 23:44:35 | Statements committed (961cebc) |
| 23:54:21 | RFC 3161 stamp of the statements |
| 00:00:41 | Pre-proof prompt committed (76cdff1) |
| 00:02–00:05 | Pre-proof referees' scratch files (/tmp/vtrefA, /tmp/vtrefB) |
| 00:15:08 | Reviews committed (4550529) |
| 00:24:23 | Reviews stamped (RFC 3161 ×3) |
| 00:25:45 | Route, blueprint and assembly committed (52188e4) |
| 00:29:09 | Route referee report committed (c24d0ea) |
| 00:41:04 | Proof committed (d261c19) |
| 00:41:17 – 02:44:23 | Replay on d261c19 |

- **Draft of the part.** The lead's draft (scratchpad `vtdraft/VectorParts.lean`) was created at 00:26:46. That is after the review stamp and after the route commit. It is identical to the committed part apart from the licence header and module docstring.
- **Route referee.** Its scratch files (/tmp/vtroute) date from 00:27:03 to 00:27:44.
- **Build.** `VectorParts.olean` was built at 00:29:36, 27 seconds after c24d0ea.
- **Replay "alone".** No file in /tmp changed during the replay window.
- **HEAD vs replayed commit.** HEAD 09e4bc7 differs from d261c19 only in non-Lean files (the replay record and two prompts).
- **Verdict on order.** Everything is consistent with "statements frozen and reviewed before any proof" and with "route review committed before the part entered the repository, draft in the scratchpad meanwhile".

## Findings
**MINOR-1. Stale user-facing docs.**
- `docs/which-theorem.md:59` still lists "vector-valued (matrix) amplitudes" under "Not (yet) covered". GD-C/GD/GD-F/GD-N are now covered for vector-valued amplitudes.
- `docs/design/vector-amplitudes.md:20-22` still calls the transfer "PLAUSIBLE … the Mathlib names … not yet used".
- `docs/statements.md` "Batch VT" (lines 564–606) never says the batch is proved or points to `VectorFinal.lean` or the replay.
- Lesser related items: `docs/applications.md:22` and `docs/ROADMAP.md:78` (unchecked box). Both are defensible while the VV acceptance model is deferred, but could say that GD-type bounds are done.

**MINOR-2. The route-review order claim rests on evidence the lead controls.**
- `docs/proof-VT.md:22-25` and the c24d0ea message claim the route review was committed before the proof. The support is the git DAG plus volatile file times in /tmp and the scratchpad. No third-party timestamp covers c24d0ea.
- The draft existed for the whole route review (as disclosed), and the review changed nothing in the proof. So the route review came before the proof's commit, not before the proof existed.
- The claim is true as worded. Its strength should not be read as more than that. If the claim matters, stamp the route-review commit.

**NIT-1. The Order paragraph is incomplete.** `docs/statements.md:566-569` says the sanity theorems were committed and stamped before the pre-proof reviews. At HEAD the file (`95eed172…`) is the post-review version: three theorems were added in 4550529 in answer to the reviews, and that version was stamped in 20261109T002419Z. The file the reviewers saw was `b9fa7e16…` (stamp 961cebc). This is disclosed in the answers file and the commit message, but not in the Order paragraph.

**NIT-2. No compiled non-vacuity amplitude in the repository.** The sanity theorems instantiate phase data only, and no compiled VT datum exhibits a nonzero E-valued amplitude that meets the hypotheses. I compiled one (/tmp/vtpostA/nonvac.lean); something similar could be added to `VectorSanity.lean`.

**NIT-3. Clarification 6 has no compiled check in the repository.** Pre-proof review A's MINOR-3 suggested a snippet for the local `Matrix.linftyOp*` instances; it was answered with doc text only. I verified that it elaborates (/tmp/vtpostA/matrix.lean).

**NIT-4. Where the polymorphic transfer lives.** The universe-polymorphic transfer promised in clarification 7 is `OscInt.VectorAux.transfer` (`OscInt/Front/VectorParts.lean:75`). It sits outside `OscInt.API`, and it is phrased with θ and B rather than per statement, so a user in a higher universe has to re-run the assembly in `VectorAssembly.lean`. This is documented in `VectorFinal.lean:15-16`.
