# Status

> **Review paths (2026-11-10).** Many rows cite verbatim referee reports under `review/`. Those reports were removed
> from the current tree under the owner's privacy rule (`docs/lessons.md` 46; `review/README.md`). Each cited path can be
> read with `git show 58a86d0:<path>`, and the lead's answers files under `review/` still state every finding.

One line per statement. A status is derived from evidence files, never typed as a claim; "machine-checked as stated"
requires every row of the trust chain (README) for that statement.

| Statement | Lean | Statement frozen | Blind review | Proof | Replay | Status |
|---|---|---|---|---|---|---|
| S1 1D van der Corput | `OscInt.vanDerCorput_one/two/three` | yes, stamp `20261105T203058Z-7516eb518dce` (pinned) | pre: FAITHFUL ×3; post: FAITHFUL ×3, scope full | yes | 7 kernel runs + comparator | machine-checked as stated |
| S2.1 non-stationary phase | `OscInt.nonStationary` | yes, stamp `20261105T234456Z-533ae0272521` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes | 7 kernel runs + comparator | machine-checked as stated |
| S2.2 nondegenerate stationary phase | `OscInt.stationaryPhase` | yes, stamp `20261105T234456Z-533ae0272521` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes | 7 kernel runs + comparator | machine-checked as stated |
| S3 uniform fold | `OscInt.fold` | yes, stamp `20261105T234456Z-533ae0272521` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2 to the docs (one referee: FAITHFUL-WEAKER than the classical form), scope full | yes | 7 kernel runs + comparator | machine-checked as stated (fold condition on all of K) |
| S4.1 uniform D4 bound | `OscInt.d4Bound` | yes, stamp `20261106T033706Z-63564a8d78cd` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2 to the docs, FAITHFUL-WEAKER than the classical form (D4⁺ only, as the brief), scope full | yes | 7 kernel runs + comparator | machine-checked as stated (hyperbolic umbilic D4⁺) |
| S4.1′ uniform D4 bound, both umbilics (`disc ≠ 0`) | `OscInt.d4BoundNe` | yes, stamp `20261106T081634Z-e2d7771c358e` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2 (STRONGER than the brief), scope full | yes (same parts as S4.1, assembly `d4BoundNe_of`) | 7 kernel runs + comparator (`docs/replay/2026-11-06-S4b-verify-all.txt`, a71b318) | machine-checked as stated |
| S4.2 D4 limit t^{2/3}∫e^{itφ}A → c_C A(0), c_C Gamma-free (the brief's closed form is S4.4) | `OscInt.d4Limit` | yes, stamp `20261106T081634Z-e2d7771c358e` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full (part of the brief's S4, which also needs S4.4) | yes (route `docs/proof-S42.md`, refereed; parts by agents X, Y, Z, Q2; assembly by the lead) | 7 kernel runs + comparator (`docs/replay/2026-11-06-S4b-verify-all.txt`, a71b318) | machine-checked as stated |
| S4.3 c_C > 0 (alternating series, Gamma-free) | `OscInt.d4ConstantPos` | yes, same stamp | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes (route `docs/proof-S43.md`, refereed; parts by agents U, V, W) | 7 kernel runs + comparator (`docs/replay/2026-11-06-S4b-verify-all.txt`, a71b318) | machine-checked as stated; proof Gamma/Beta/Mellin-free by name (`GammaFree.lean`, transitive through types and proofs, 43 612 constants; first committed 94f7657 without following proofs, corrected with the proof in e89b610, re-run independently by the adversarial referee) |
| S4.4 closed forms of c_C | `OscInt.d4ConstantClosedForm` | yes, stamp `20261106T081634Z-e2d7771c358e` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes (route `docs/proof-S44.md`, refereed; parts by agents M, N, O, T, K; E4, E7 and the assembly by the lead) | 7 kernel runs + comparator (`docs/replay/2026-11-06-S44-verify-all.txt`, 1c7ebe3, verify-all PASS) | machine-checked as stated |
| F1 amplitude bounds from `ContDiff` and compact support (front end) | `OscInt.API.ampBoundOfContDiff` | yes, stamp `20261107T012459Z-2d5356432156` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes (bridge in `OscInt/API.lean`; drafted before the review, disclosed) | 7 kernel runs + comparator (`docs/replay/2026-11-07-API1-verify-all.txt`, 2ddcbe0, verify-all PASS) | machine-checked as stated (no "statement before proof" claim) |
| F2 D4 limit with the closed-form constant, `ContDiff` amplitudes (front end; the brief's S4 limit with its constant as one theorem) | `OscInt.API.d4LimitClosedForm` | yes, same stamp | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full (FAITHFUL-STRONGER than the brief's limit: elliptic branch, C² amplitudes) | yes (from S4.2, S4.4, F1; same disclosure) | same record | machine-checked as stated (no "statement before proof" claim) |
| C1 `dd` ↔ `iteratedFDeriv ℝ 2` | `OscInt.API.dd_iteratedFDeriv` | yes, stamp `20261107T101640Z-4acb308f54f4` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes (agent D) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C2 `ddd` ↔ `iteratedFDeriv ℝ 3` | `OscInt.API.ddd_iteratedFDeriv` | yes, same stamp | same | yes (agent D) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C3 `hessDet` = det of the Hessian matrix | `OscInt.API.hessDet_eq_det` | yes, same stamp | same | yes (agent D) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C4 `cubicCoeffs` ↔ D³φ(0)[κ,κ,κ]/6 | `OscInt.API.cubicCoeffs_eq` | yes, same stamp | same | yes (agent D) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C5 `disc` = `Cubic.discr` | `OscInt.API.disc_eq_cubic_discr` | yes, same stamp | same (referee A proved it in its scratch during the pre-proof review, disclosed) | yes (agent Q) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C6 `disc ≠ 0` ↔ isolated critical point | `OscInt.API.disc_ne_zero_iff_isolated` | yes, same stamp | same | yes (agent Q; sympy certificates re-checked by `linear_combination`) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C7 `FoldOrNondeg` ↔ kernel/rank form | `OscInt.API.foldOrNondeg_iff` | yes, same stamp | same | yes (core: agent F; assembly: lead) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C7′ `FoldOrNondeg` from `HasFDerivAt` data | `OscInt.API.foldOrNondeg_of_hasFDeriv` | yes, same stamp | same | yes (agent F) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated; hypotheses not yet witnessed by an explicit example in Lean |
| C8 `GradLower` ↔ Euclidean / max-norm bounds | `OscInt.API.gradLower_iff` | yes, same stamp | same | yes (agent N) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| C9 `AmpBound` ↔ `ContDiff` + `HasCompactSupport` | `OscInt.API.ampBound_conv` | yes, same stamp | same | yes (agent N) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| FE-S2.1 non-stationary phase, Mathlib idiom | `OscInt.API.nonStationaryFE` | yes, same stamp | same | yes (lead, from S2.1 and C8) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| FE-S2.2 stationary phase, Mathlib idiom | `OscInt.API.stationaryPhaseFE` | yes, same stamp | same | yes (lead, from S2.2 and C3) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| FE-S3 uniform fold, Mathlib idiom | `OscInt.API.foldFE` | yes, same stamp | same | yes (lead, from S3 and C7) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| FE-S4.1′ uniform D4, Mathlib idiom | `OscInt.API.d4BoundFE` | yes, same stamp | same | yes (lead, from S4.1′, C1, C4, C5) | 7 kernel runs + comparator (`docs/replay/2026-11-07-session4-final-verify-all.txt`, c462966, verify-all PASS) | machine-checked as stated |
| S2.2F nondegenerate stationary phase, uniform over a compact family | `OscInt.API.stationaryPhaseFamily` | yes, stamp `20261108T002603Z-9d03130c8f3a` (pinned) | pre: FAITHFUL ×2 (sanity layer MAJOR addressed by conditional sanity theorems, one-time waiver ratified by the owner 2026-11-09, `review/2026-11-08-API3-pre-proof-answers.md`); post: FAITHFUL ×2, scope full (`review/2026-11-08-API3-post-proof-{A,B}.md`); adversarial: three MAJOR on the sanity layer, addressed (`review/2026-11-08-API3-answers.md`) | yes (lead; re-assembly of the proved S2.2/S3 parts) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| S3c uniform fold, classical hypothesis (critical points only) | `OscInt.API.foldCrit` | yes, same stamp | same | yes (lead; re-assembly) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| C10 joint smoothness ⇒ `FamilyCk` | `OscInt.API.familyCk_of_uncurry` | yes, same stamp | same | yes (agent P1) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S2.1L non-stationary phase, family, local smoothness | `OscInt.API.nonStationaryLocal` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S2.2L stationary phase, family, local smoothness | `OscInt.API.stationaryPhaseLocal` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S3L fold, family, local smoothness, classical hypothesis | `OscInt.API.foldLocal` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S4.1′L uniform D4, local smoothness | `OscInt.API.d4BoundLocal` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S2.1l non-stationary phase, one phase, local smoothness | `OscInt.API.nonStationaryOn` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S2.2l stationary phase, one phase, local smoothness | `OscInt.API.stationaryPhaseOn` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| FE-S3l fold, one phase, local smoothness, classical hypothesis | `OscInt.API.foldOn` | yes, same stamp | same | yes (lead; bridge with the cut-off of agent P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session5-API3-verify-all.txt`, a638f70, verify-all PASS) | machine-checked as stated (one-time waiver of CONTRIBUTING step 5 for a test-layer MAJOR, ratified by the owner 2026-11-09; `review/2026-11-08-API3-answers.md`, M3) |
| GD-C global decay, classification at critical points | `OscInt.API.globalDecayCrit` | yes, stamp `20261108T094842Z-edf7787a2845` (pinned) | pre: FAITHFUL and TRUE ×2 (`review/2026-11-08-GD-pre-proof-{A,B}.md`; reviews stamped `20261108T102629Z-8c8d7b090adb` before any proof); post: FAITHFUL ×2, scope full (`review/2026-11-08-GD-post-proof-{A,B}.md`); adversarial: no BLOCKER/MAJOR, answered (`review/2026-11-08-GD-post-proof-answers.md`) | yes (lead; assembly `crit_induction` on the parts of agent GD-P1) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| GD global decay, all linear terms | `OscInt.API.globalDecay` | yes, same stamp | same | yes (lead; GD-C plus large linear terms (agent GD-P1)) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| GD-F all points fold or nondegenerate, all linear terms | `OscInt.API.globalFold` | yes, same stamp | same | yes (lead) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| GD-N all points nondegenerate, all linear terms | `OscInt.API.globalNondeg` | yes, same stamp | same | yes (lead) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| SH sharpness lemma | `OscInt.API.sharpness` | yes, same stamp | same | yes (lead) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| T1 torus unfolding weight | `OscInt.API.torusUnfold` | yes, same stamp | same | yes (agent GD-P2) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| T6 2D lattice-Laplacian dispersive decay t^{-2/3} | `OscInt.API.latticeLaplacianDecay` | yes, same stamp | same | yes (lead; classification by agent GD-P3) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| T6L its diagonal leading term | `OscInt.API.latticeLaplacianLimit` | yes, same stamp | same | yes (agent GD-P4) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session6-GD-verify-all.txt`, c62a621, verify-all PASS) | machine-checked as stated (replay of c62a621; the pull request's head is replayed by CI `verify / verdict`) |
| T0E explicit 1D lattice-kernel bound (content only for t > 518) | `OscInt.API.latticeKernel1Explicit` | yes, stamp `20261108T160847Z-4a183530559f` (pinned) | pre: FAITHFUL and TRUE ×2 (`review/2026-11-08-LE-pre-proof-{A,B}.md`; reviews stamped `20261108T164514Z-c91a9a8bb0b6`); post: FAITHFUL ×2, scope full (`review/2026-11-08-LE-post-proof-{A,B}.md`); adversarial: no BLOCKER/MAJOR, answered (`review/2026-11-08-LE-post-proof-answers.md`) | yes (lead; from S1.2, S1.3) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session7-LE-verify-all.txt`, a1d2a64, verify-all PASS) | machine-checked as stated (replay of a1d2a64; one-time waiver of CONTRIBUTING step 5 for a documentation-only MAJOR, ratified by the owner 2026-11-09; step 5 now provides for this case) |
| T6F the 2D lattice kernel factorises | `OscInt.API.latticeKernelFactor` | yes, same stamp | same | yes (lead) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session7-LE-verify-all.txt`, a1d2a64, verify-all PASS) | machine-checked as stated (replay of a1d2a64; one-time waiver of CONTRIBUTING step 5 for a documentation-only MAJOR, ratified by the owner 2026-11-09; step 5 now provides for this case) |
| T6E explicit constant for T6, (A+B)² ≈ 4754 (content only for t > 1321) | `OscInt.API.latticeLaplacianExplicit` | yes, same stamp | same | yes (lead) | 7 kernel runs + comparator (`docs/replay/2026-11-08-session7-LE-verify-all.txt`, a1d2a64, verify-all PASS) | machine-checked as stated (replay of a1d2a64; one-time waiver of CONTRIBUTING step 5 for a documentation-only MAJOR, ratified by the owner 2026-11-09; step 5 now provides for this case) |
| GD-C-V GD-C, Banach-valued amplitudes | `OscInt.API.globalDecayCritVec` | yes, stamp `20261108T235416Z-961cebc296ef` (pinned) | pre: FAITHFUL and TRUE ×2 (`review/2026-11-08-VT-pre-proof-{A,B}.md`; reviews stamped `20261109T002419Z-45505299011a`); route referee (`review/2026-11-09-VT-route-referee.md`); post: FAITHFUL ×2, scope full (`review/2026-11-09-VT-post-proof-{A,B}.md`); adversarial: no BLOCKER on VT, answered (`review/2026-11-09-VT-post-proof-answers.md`) | yes (lead; duality from GD-C) | 7 kernel runs + comparator (`docs/replay/2026-11-09-session7-VT-verify-all.txt`, d261c19, verify-all PASS) | machine-checked as stated (replay of d261c19) |
| GD-V GD, Banach-valued amplitudes | `OscInt.API.globalDecayVec` | yes, same stamp | same | yes (lead; duality from GD) | 7 kernel runs + comparator (`docs/replay/2026-11-09-session7-VT-verify-all.txt`, d261c19, verify-all PASS) | machine-checked as stated (replay of d261c19) |
| GD-F-V GD-F, Banach-valued amplitudes | `OscInt.API.globalFoldVec` | yes, same stamp | same | yes (lead; duality from GD-F) | 7 kernel runs + comparator (`docs/replay/2026-11-09-session7-VT-verify-all.txt`, d261c19, verify-all PASS) | machine-checked as stated (replay of d261c19) |
| GD-N-V GD-N, Banach-valued amplitudes | `OscInt.API.globalNondegVec` | yes, same stamp | same | yes (lead; duality from GD-N) | 7 kernel runs + comparator (`docs/replay/2026-11-09-session7-VT-verify-all.txt`, d261c19, verify-all PASS) | machine-checked as stated (replay of d261c19) |
| S1.k k-th derivative van der Corput, constant 5·2^{k−1} − 2 | none yet (challenge `OscInt.API.vdCk`) | yes, stamp `20261109T201548Z-fcb46d9a6239` (pinned) | pre: FAITHFUL and TRUE ×2 (`review/2026-11-09-A3-pre-proof-{A,B}.md`; answers `review/2026-11-09-A3-pre-proof-answers.md`; reviews stamped `20261109T214121Z-47c1360ccd6f`) | no | — | stated and reviewed, not proved |
| S5.1 uniform stable-cusp bound t^{−3/4} | none yet (challenge `OscInt.API.cuspBound`) | yes, same stamp | same | no | — | stated and reviewed, not proved |
| S5.1′ uniform cusp (A3) bound t^{−3/4} | none yet (challenge `OscInt.API.cuspBoundGen`) | yes, same stamp | same | no | — | stated and reviewed, not proved |
| T0E′ cube-root bound for the 1D lattice kernel, 8(1 + √7)/3 · t^{−1/3} (content for t > 3.70; implies T0E) | `OscInt.API.latticeKernel1CubeRoot` | yes, stamp `20261110T234417Z-0532b1cf8880` (pinned) | pre: FAITHFUL and TRUE ×2 (answers `review/2026-11-10-LE2-pre-proof-answers.md`; reviews answered and stamped `20261111T005634Z-bf8af89bc235`); post: FAITHFUL ×2, scope full, parts SOUND; adversarial: three MAJOR (documentation), answered (`review/2026-11-11-LE2-post-proof-answers.md`) | yes (parts by proof agents after the route review, assembly by the lead; route `docs/proof-LE2.md`, refereed; one recorded deviation in P-r8) | 7 kernel runs + comparator-LE2 accepted (`docs/replay/2026-11-11-session10-LE2-verify-all.txt`, 68aec60; verify-all INCOMPLETE only because comparator-A3 has no solution yet) | machine-checked as stated (replay of 68aec60) |
| T6E′ cube-root constant for T6, (8(1 + √7)/3)² ≈ 94.52, t > 0 | `OscInt.API.latticeLaplacianCubeRoot` | yes, same stamp | same | yes (lead: T6F and T0E′) | 7 kernel runs + comparator-LE2 accepted (`docs/replay/2026-11-11-session10-LE2-verify-all.txt`, 68aec60; verify-all INCOMPLETE only because comparator-A3 has no solution yet) | machine-checked as stated (replay of 68aec60) |
| TdF the d-dimensional hypercubic lattice kernel factorises | none yet (challenge `OscInt.API.hypercubicKernelFactor`) | yes, stamp `20261112T120616Z-c56beb57ff8c` (pinned) | pre: FAITHFUL and TRUE ×2 (answers `review/2026-11-12-HC-pre-proof-answers.md`; reviews answered and stamped `20261112T123958Z-8e4f8c5cbcaf`) | no | — | stated and reviewed, not proved |
| TdE′ hypercubic kernel in every dimension, (8(1 + √7)/3)^d t^{−d/3} | none yet (challenge `OscInt.API.hypercubicCubeRoot`) | yes, same stamp | same | no | — | stated and reviewed, not proved |

T6, T6L prior art (2026-11-08, session 7): both are classical, because the 2D kernel factorises into two 1D Bessel
kernels; the rows above are unchanged (the proofs are unaffected), but they claim "machine-checked", not new
mathematics, and are not evidence for non-separable symbols (`docs/prior_art.md`, "Lattice kernels").

Batch LE (session 7, 2026-11-08). Statements `OscInt/Statements/LatticeExplicit.lean`, stamp
`stamps/20261108T160847Z-4a183530559f` (RFC 3161 ×3 at 16:08:50Z); numeric pre-registration
`docs/prereg/2026-11-08-LE-lattice-constants.md` (PASS); blind pre-proof reviews FAITHFUL and TRUE ×2, stamped with the
answers in `stamps/20261108T164514Z-c91a9a8bb0b6` (16:45:19Z). That no proof existed before then rests on git order and
the lead's session record (RFC 3161 bounds when the statements and reviews existed, not when proofs did not; adversarial
review m5). The route referee ran while the parts were being written, so "route reviewed before any part was proved"
is not claimed (`docs/proof-LE.md`, lessons 42). Proofs: lead (parts from the proved S1.2/S1.3, Fubini for T6F).
Record `docs/replay/2026-11-08-session7-LE-verify-all.txt` (a1d2a64, verify-all PASS 9/9). Post-proof FAITHFUL ×2;
adversarial no BLOCKER/MAJOR. The constants are explicit but weak: they beat the trivial bounds only for t > 518 (1D)
and t > 1321 (2D) (`docs/statements.md`, Batch LE, clarification 6). Process: referee A's pre-proof MAJOR asked for a
documentation change only and was answered without re-freeze; ratified by the owner on 2026-11-09 as a one-time
waiver, and CONTRIBUTING step 5 now provides for documentation-only MAJORs. Reviewers
are AI agents; no human has read these statements (`docs/policy.md`).

Batch VT (session 7, 2026-11-09). Statements `OscInt/Statements/Vector.lean` (the four global decay estimates for
amplitudes in any complex Banach space `E : Type`, one constant for every E), stamp `stamps/20261108T235416Z-961cebc296ef`
(RFC 3161 ×3 at 23:54:21Z); blind pre-proof reviews FAITHFUL and TRUE ×2, stamped with the answers in
`stamps/20261109T002419Z-45505299011a` (00:24:23Z); route review committed before the part's proof entered the repository
(commit order; the lead's draft was in the scratchpad meanwhile). Proof: duality from the proved GD statements
(`OscInt/Front/VectorParts.lean`). Record `docs/replay/2026-11-09-session7-VT-verify-all.txt` (d261c19, PASS 9/9).
Post-proof FAITHFUL ×2. The owner's acceptance test for VV (a non-separable two-band model compiled end to end) is NOT
met: the candidate QWZ m = 3 has exact cusp points (erratum, `docs/design/vector-amplitudes.md` §6). Reviewers are AI
agents; no human has read these statements.

Pipeline skeleton (M0): `OscInt.skeleton_two_mul` builds, audits clean (1 of 1) and replays in six kernels
(`build/replay/summary.txt` from `make lean-replay`; the CI run on each push records it).

S1 (2026-11-05). `OscInt.vanDerCorput_one`, `_two`, `_three` prove `VdC1Statement`, `VdC2Statement`,
`VdC3Statement` (constants 3, 8, 18; amplitude form; linear term in k = 2, 3). Evidence: axiom audit 36/36; statement
types checked syntactically; commitments recomputed and equal to the pinned stamp; `lake comparator --paranoid`
accepted against the stamped challenge export; replay by Lean's kernel (default, paranoid), nanoda, con-leche,
con-ron and lean4lean (`docs/replay/2026-11-05-M1-verify-all.txt`); blind pre-proof and post-proof reviews FAITHFUL
(`review/`), adversarial review answered. Proof route ported from J. Roos and M. Praveen, `roos-j/lean-oscillatory`
(Mathlib PR #39406), by four proof agents (parts P0–P4) and the lead (statements, blueprint, assembly). Relative to
Stein the theorems are weaker in the phase (φ′ differentiable; lower derivatives continuous up to the endpoints) and
more general in the amplitude (ψ′ only integrable). Reviewers are AI agents; no human has read the statements yet.

S2/S3 (2026-11-06). Proved: `OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold` (route
`docs/proof-S2S3.md`, parts by proof agents G1–G3 and H1–H6, assembly by the lead). Caveat on the review evidence:
referee calibration round 1 used short S1 statements; the S2/S3 statements are longer and use more Mathlib
machinery, a regime round 1 did not test (`docs/calibration.md`).

Final record for S2/S3: `docs/replay/2026-11-06-S2S3-final-verify-all.txt` (commit d932c0d, PASS 8/8: axiom audit
276/276, six commitments equal to the pinned stamps, comparator accepted both configurations, replay by per-module
`leanchecker` and six export kernels, both pinned stamps verified). Reviews: `review/2026-11-05-S2S3-pre-proof-{A,B}.md`,
`review/2026-11-05-S2S3-proof-route.md`, `review/2026-11-06-S2S3-post-proof-{A,B}.md`, `review/2026-11-06-S2S3-adversarial.md`
with answers in `review/2026-11-06-S2S3-answers.md`. "As stated" includes S3's hypothesis at every point of K
(`docs/statements.md`, clarification of 2026-11-06). Reviewers are AI agents; no human has read the statements.

S4.1 (2026-11-06). Proved: `OscInt.d4Bound` (route `docs/proof-S4.md`, refereed in
`review/2026-11-06-S4-proof-route.md`; blueprint `Blueprint/D4.lean`, parts D1–D9 by proof agents P, Q, R, S;
assembly `OscInt.D4.d4Bound_of` by the lead, from S3 and S2.1). Record: `docs/replay/2026-11-06-S4-verify-all.txt`
(commit a0b1fde, PASS 8/8: axiom audit 365/365, seven commitments equal to the pinned stamps, comparator accepted all
three configurations, per-module `leanchecker` and six export kernels); CI run 42172708736 green on a0b1fde. Reviews:
`review/2026-11-06-S4-pre-proof-{A,B}.md`, `review/2026-11-06-S4-post-proof-{A,B}.md`,
`review/2026-11-06-S4-adversarial.md`, answers in `review/2026-11-06-S4-answers.md`. Scope: `disc < 0` is the
hyperbolic umbilic D4⁺, which is the brief's case ("an isolated critical point and negative discriminant"); the
proof uses only `disc ≠ 0`, so D4⁻ is a small extension if the owner widens the statement. Non-vacuity:
`OscInt/D4/Sanity.lean`, `OscInt/D4/Bite.lean`.

S4.1′–S4.4 (2026-11-06). Decisions: `docs/decisions/2026-11-06-S4.md` (c_C defined Gamma-free; widening to
`disc ≠ 0` as a new statement; nanoda built from source in CI). S4.1′ (`OscInt.d4BoundNe`), S4.2 (`OscInt.d4Limit`)
and S4.3 (`OscInt.d4ConstantPos`) are machine-checked as stated: record `docs/replay/2026-11-06-S4b-verify-all.txt`
(a71b318: per-configuration lines "comparator-S41w/S42/S43.json accepted against stamps/20261106T081634Z-e2d7771c358e",
six kernels, axiom audit 458/458; the overall result is INCOMPLETE only because S4.4 has no proof), CI run
42200801140 green on a71b318 (including nanoda built from source). The brief's S4 limit with its constant
Γ(1/3)²/(√3|Disc|^{1/6}) is S4.2 ∧ S4.4 (Disc < 0 clause); S4.4 is not proved, so that form is open (superseded: S4.4 was proved later, see the S4.4 row); "c_C ≠ 0" is
S4.3 (proved, Gamma-free by name). Reviews: `review/2026-11-06-S4b-pre-proof-{A,B}.md`,
`review/2026-11-06-S43-proof-route.md`, `review/2026-11-06-S42-proof-route.md`, `review/2026-11-06-S4b-post-proof-{A,B}.md`,
`review/2026-11-06-S4b-adversarial.md`; answers in `review/2026-11-06-S4b-pre-proof-answers.md` and
`review/2026-11-06-S4b-answers.md`.

S4.4 (2026-11-06, session 3). Proved: `OscInt.d4ConstantClosedForm` (route `docs/proof-S44.md`, refereed in
`review/2026-11-06-S44-proof-route.md`: all parts TRUE, one BLOCKER, a name clash in the blueprint, fixed before any
agent started; blueprint `Blueprint/D4ClosedForm.lean`; parts E1 agent M, E2 agent N, E3 agent O, E5 agent T,
E6a–c agent K, reports `review/2026-11-06-S44-agent-reports.md`; E4, E7 and the assembly `d4ConstantClosedForm_of`
by the lead, the assembly compiled against the parts before any part was proved). The hand-off's route for the cosine
moment needed `Complex.integral_cpow_mul_exp_neg_mul_Ioi` with a complex rate, which that lemma does not take
(lessons 19); the proof uses a real-variable route through the Beta integral instead. Record
`docs/replay/2026-11-06-S44-verify-all.txt` (1c7ebe3): `make verify-all` RESULT PASS, 9 of 9 steps, the first full PASS
(axiom audit 521/521; comparator accepted all seven configurations; eleven commitments equal their pinned stamps;
per-module `leanchecker` and six export kernels). Non-vacuity on generic data: `OscInt.d4Constant_example`
(x³ + 2x²y + 3xy² + 5y³, disc −367). With S4.2 this is the brief's S4 limit with its closed-form constant. Reviews:
post-proof FAITHFUL ×2, scope full, pinned to commitment `3f089384…` (`review/2026-11-07-S44-post-proof-{A,B}.md`; each
checked the closed forms numerically on generic cubics of both signs to ≤ 2·10⁻¹¹); adversarial
`review/2026-11-07-S44-adversarial.md`: no finding on S4.4 or its trust chain; one BLOCKER and four MAJOR on the new
downstream checker, answered in `review/2026-11-07-S44-answers.md`. Citation: the brief's S4 limit with its constant
is `OscInt.d4Limit` ∧ `OscInt.d4ConstantClosedForm`, with `OscInt.d4ConstantPos` for c_C ≠ 0 and for the
convergence of the improper integral (referee NITs).

Front-end batch 1, F1 and F2 (2026-11-07, session 3). Statements `OscInt/Statements/FrontEnd.lean`, stamped
`20261107T012459Z-2d5356432156` and pinned; blind statement review FAITHFUL ×2 (`review/2026-11-07-API1-pre-proof-{A,B}.md`;
each referee wrote its own bridge independently); proofs `OscInt.API.ampBoundOfContDiff`, `OscInt.API.d4LimitClosedForm`
in `OscInt/API.lean`; non-vacuity and bite `OscInt/Front/Sanity.lean` (elliptic and generic phases, an independent
elliptic value, a nonzero limit); record `docs/replay/2026-11-07-API1-verify-all.txt` (2ddcbe0, verify-all PASS, axiom
audit 536/536, comparator-API1 accepted); post-proof FAITHFUL ×2 (`review/2026-11-07-API1-post-proof-{A,B}.md`; answers
`review/2026-11-07-API1-answers.md`). Disclosure: the bridge proofs were drafted in the lead's scratch directory before
the stamp and review, so "statement fixed before the proof" is not claimed for F1 and F2.

Front-end batch 2 (2026-11-07, session 4). Statements `OscInt/Statements/Convert.lean` (14), stamped
`20261107T101640Z-4acb308f54f4` (RFC 3161 ×3, 10:16:43Z) and pinned; blind statement review FAITHFUL ×2
(`review/2026-11-07-API2-pre-proof-{A,B}.md`, answers `…-pre-proof-answers.md`); route `docs/proof-API2.md`; parts by
proof agents D (C1–C4), Q (C5, C6), F (fold core, C7′), N (C8, C9), assembly and front ends by the lead
(`OscInt/Front/Convert.lean`, from `OscInt.nonStationary`, `stationaryPhase`, `fold`, `d4BoundNe`); post-proof
FAITHFUL ×2, scope full (`review/2026-11-07-API2-post-proof-{A,B}.md`); adversarial review (no BLOCKER, six MAJOR,
answered in `review/2026-11-07-API2-answers.md`). Record `docs/replay/2026-11-07-session4-final-verify-all.txt`
(c462966, verify-all PASS); independently, CI run 42373634892 on c462966: job `verify` (full verify-all on a fresh
runner, plus nanoda built from source) and job `quick` green. Non-vacuity: `OscInt/Front/ConvertSanity.lean`, `OscInt/Front/Examples.lean`,
`examples/consumer/ConsumerFormula.lean` (the P1 acceptance: FE-S3 and FE-S4.1′ on phases given only by a formula).
Order: the statements are timestamped; that the reviews preceded the Lean proofs rests on git order (reviews not
stamped; `docs/statements.md`, correction of 2026-11-07). C7′'s hypotheses are not yet witnessed by an explicit
example in Lean. Reviewers are AI agents; no human has read the statements.

Front-end batch 3 (API3, session 5, 2026-11-08). Statements `OscInt/Statements/Family.lean`, stamp
`stamps/20261108T002603Z-9d03130c8f3a` (RFC 3161 ×3 at 00:26:05Z); blind pre-proof reviews FAITHFUL and TRUE ×2, stamped
with the answers, the conditional sanity file and the route in `stamps/20261108T010546Z-7bb457958327` (01:05:48Z)
before any proof was committed (that none existed in scratch rests on the lead's statement). Proofs: S2.2F and S3c by
re-assembly of the proved internal S2.2/S3 parts (`OscInt/Front/Family.lean`, so they rest on those parts, not on the
frozen S2.2/S3 constants); C10 (agent P1); the cut-off (agent P2); seven bridges (`OscInt/Front/Local.lean`). Record:
`docs/replay/2026-11-08-session5-API3-verify-all.txt` (a638f70, verify-all PASS 9/9). Post-proof FAITHFUL ×2; adversarial
answered in `review/2026-11-08-API3-answers.md`. Process deviation, ratified by the owner on 2026-11-09 as a one-time waiver (option (iii) of
`docs/decisions/2026-11-08-step5-memo.md`; CONTRIBUTING step 2 amended): the pre-proof MAJOR on
the sanity layer (lessons 11) was addressed by sanity theorems through the statement constants
(`OscInt/Front/FamilySanity.lean`, `FamilySanity2.lean`; planted controls `docs/replay/2026-11-08-API3-sanity-plants.txt`,
plant files `docs/replay/plants/2026-11-08-API3/`; falsity of the plants on the data proved in
`examples/consumer/ConsumerLocalChecks.lean`) instead of a re-freeze (CONTRIBUTING step 5). Such theorems cannot detect
a plant that weakens a hypothesis. Reviewers are AI agents; no human has read these statements.
