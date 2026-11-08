c98f4962f9fbf7d8158fc5b4acbb15d965885488

# GD post-proof review, referee B (fresh context)

Prompt: `review/prompts/GD-post-proof.md`. HEAD = c98f496 (checked with `git rev-parse HEAD`, it has not moved).
Replay record: `docs/replay/2026-11-08-session6-GD-verify-all.txt` (c62a621). Lean runs were scratch only under
`/tmp/ppB/`, one process at a time, `nice -n 10 lake env lean -DautoImplicit=false`. I wrote nothing in the repository
and ran no `make` or `lake build`.

## Summary

All eight theorems are **FAITHFUL, scope full** against `docs/statements.md` ("Batch GD", lines 418-493, with its
post-stamp clarification). There are no BLOCKER or MAJOR findings. Two MINOR findings concern evidence and docs, not the
theorems.

## 0. Integrity of the frozen layer and replay

- `OscInt/Statements/Global.lean` has SHA-256 `edaaf9c6…a8d78cd`, equal to the entry in
  `stamps/20261108T094842Z-edf7787a2845/manifest.txt`. `stamps/pins.txt` pins all eight constants and
  `challenge:comparator-GD.json` to that stamp. Every `OscInt/Statements/*.lean` and `Challenge/*.lean` at HEAD matches
  that manifest (16/16 OK, so the imported constants such as `FoldOrNondegMatrix`, `hessianMatrix` and
  `d4ClosedConstant` are also unchanged). `comparator-GD.json` (`76172b5b…`) and `Challenge/Global.lean` (`bfd5199d…`)
  match too.
- `git diff c62a621 HEAD -- '*.lean'` adds only licence-header comments: 98 files, 704 insertions, 0 deletions, and
  every added line is a header line. `Challenge/*.lean` is not touched. The licence record
  (`docs/replay/2026-11-08-session6-licence-headers-checks.txt`) shows the GD export as `d64efded…`, byte-identical
  to the stamped `challenge-export … GD.ndjson` (manifest line 512), and 45/45 commitments matching their stamps.
- `OscInt/Front/GlobalSanity.lean` at HEAD (`f71a05e5…`) differs from both stamps (`b6ebea31…` at the GD stamp,
  `e9e08548…` at the 8c8d7b0 stamp). `git diff 8c8d7b0 HEAD` on that file adds only the 7-line licence header.
- Replay (c62a621): RESULT PASS 9/9, as listed below.
  - TYPE-OK lines 232-239 cover all eight `OscInt.API.*` against their `*Statement` constants. `StatementTypes.lean`
    lines 65-72 check `ci.type == mkConst s []`, which is syntactic equality.
  - Axiom audit 890/890.
  - Per-module leanchecker PASS for every GD module, from `GlobalAssembly` through `LatticeSymbol` and
    `Blueprint.Global`.
  - Six export kernels.
  - Line 554: `comparator-GD.json accepted against stamps/20261108T094842Z-edf7787a2845`.
- My own check at HEAD (`/tmp/ppB/check.lean`): `example : XStatement := OscInt.API.x` elaborates for all eight.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all eight. I also checked by `rfl` that `∞` under
  `open scoped ContDiff` is `((⊤ : ℕ∞) : WithTop ℕ∞)`, so T1 says C^∞ and not analytic.
- A grep of the GD proof files (`GlobalFinal`, `GlobalAssembly`, `GlobalLocal`, `Torus`, `Sharpness`,
  `LatticeKernel`, `LatticeLimit`, `LatticeFinal`, `LatticeSymbol`) found no `sorry`, `axiom`, `unsafe`,
  `implemented_by`, `extern`, `native_decide`, `elab`, `macro`, `opaque` or `set_option` other than heartbeats.

## 1-2. Per-theorem type check and verdict

Each row below has: the Lean theorem, its type, and the verdict against the docs.

### GD-C
- **Theorem:** `OscInt.API.globalDecayCrit` (`OscInt/Front/GlobalFinal.lean`).
- **Type:** exactly `GlobalDecayCritStatement` (TYPE-OK l.232).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:436-439:**
  - "Ψ is C⁴ on U" is `ContDiffOn ℝ 4 Ψ U`.
  - "U open ⊇ K, K compact, K′ compact, D ⊆ U finite" is the `IsCompact`/`IsOpen`/`⊆` hypotheses and a `Finset`.
  - "D4 point" is `IsD4Point` (Global.lean:43). It matches docs line 430-432 including the factor 6 and
    `Cubic.discr ≠ 0`.
  - "Critical point of Ψ+L in K\D is a fold or nondegenerate" is `fderiv ℝ Ψ k + L = 0 → FoldOrNondegMatrix Ψ k`.
  - "Amplitude (2,K,M)" is `ContDiff ℝ 2 A`, `tsupport A ⊆ K`, and `∀ j ≤ 2, ‖iteratedFDeriv ℝ j A k‖ ≤ M`.
  - "One C for all A, M, L ∈ K′ and m ≥ 1" holds: `∃ C` precedes `∀ A M L m`.
  - The rate is `m^(-(2/3))`.

### GD
- **Theorem:** `OscInt.API.globalDecay`.
- **Type:** exactly `GlobalDecayStatement` (l.233).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:441-443:** the pointwise `Classified` is on K\D. L is unrestricted and C is uniform over L,
  which is the form a dispersive estimate needs. Clarification (2) is correct: the pointwise hypothesis equals the
  critical-point hypothesis over all L.

### GD-F
- **Theorem:** `OscInt.API.globalFold`.
- **Type:** exactly `GlobalFoldStatement` (l.234).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:445:** `FoldOrNondegMatrix` at every k ∈ K, rate m^{-5/6}, all L.

### GD-N
- **Theorem:** `OscInt.API.globalNondeg`.
- **Type:** exactly `GlobalNondegStatement` (l.235).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:446:** `det (hessianMatrix Ψ k) ≠ 0` on K. `C * M / m` is m^{-1}.

### SH
- **Theorem:** `OscInt.API.sharpness` (`Sharpness.lean`).
- **Type:** exactly `SharpnessStatement` (l.236).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:448-450:**
  - Both parts are present: ℝ → ℂ and ℕ → ℂ.
  - The hypothesis is `m^σ I(m) → c` with `c ≠ 0`.
  - The conclusion is the eventual lower bound `(‖c‖/2) m^{-σ}`, plus `¬∃ C, eventually ‖I‖ ≤ C m^{-σ'}` for every
    σ′ > σ.

### T1
- **Theorem:** `OscInt.API.torusUnfold`.
- **Type:** exactly `TorusUnfoldStatement` (l.237).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:452-453:**
  - η is real and `ContDiff ℝ ∞`, which is C^∞ (checked).
  - `tsupport η ⊆ closedBall 0 4` uses the max norm. On `ℝ × ℝ` the norm is the sup norm (`rfl` check).
  - `torusBox = Icc (-π) π ×ˢ Icc (-π) π`.
  - It holds for every continuous g that is 2π-periodic in each variable.

### T6
- **Theorem:** `OscInt.API.latticeLaplacianDecay` (`LatticeKernel.lean`).
- **Type:** exactly `LatticeLaplacianDecayStatement` (l.238).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:455-456:** the `latticeKernel` integrand is `t(cos k₁+cos k₂) + x·k` over the box. The bound is
  `∃ C, ∀ t ≥ 1, ∀ x ∈ ℤ²`. The normalisation remarks (docs 469-471) do not change |K| up to constants.

### T6L
- **Theorem:** `OscInt.API.latticeLaplacianLimit` (`LatticeFinal.lean`).
- **Type:** exactly `LatticeLaplacianLimitStatement` (l.239).
- **Verdict:** FAITHFUL, full scope.
- **Docs, statements.md:458-459:** the claim is `n^{2/3} (−1)ⁿ K(n,(n,n)) → d4ClosedConstant(−1/48)` along ℕ. The
  constant checks out as follows.
  - `d4ClosedConstant(−1/48) = Γ(1/3)²/(√3 (1/48)^{1/6}) = Γ(1/3)² 48^{1/6}/√3`, as the docs state.
  - At the critical point (π/2, π/2), the phase cos k₁+cos k₂+k₁+k₂ has the value π, which gives the factor (−1)ⁿ.
  - Its cubic part is (κ₁³+κ₂³)/6. So a = d = 1/6 and disc = −27a²d² = −1/48, consistent with clarification (5).
  - Cross-check by the folklore route: 2π·iⁿJₙ(n) per factor gives (−1)ⁿ n^{2/3} K → 4Γ(1/3)²/(2^{4/3}3^{1/3}).
    That equals 2^{2/3}3^{−1/3}Γ(1/3)², which equals Γ(1/3)²48^{1/6}/√3 (≈ 7.899). Same constant.

No theorem is WEAKER or STRONGER than the docs. Compared with the classical picture, GD-C and GD keep the rate 2/3 even
when D = ∅. That is a declared modelling choice (docs 462-463, clarification (3)), and GD-F and GD-N cover the better
rates.

## 3. Non-vacuity

What already compiles in the repository:

| Theorem | Where it is used on real data |
|---|---|
| GD | `LatticeKernel.lean:89-102`: T6's proof applies `globalDecay_of`, the same assembly as `globalDecay`, to Ψ = cos k₁+cos k₂ on K = B̄(0,4) with D = `latticeD4`. The classification `latticeSymbolFacts`, folds plus four D4 points, is proved in Lean. `ConsumerLattice.lean` (last `example`) applies `OscInt.API.globalDecay` to x³+y³ on B̄(0,1). |
| T1 | T6's proof uses its facts (`unfoldFacts`, `latticeKernel_eq`). |
| T6 | `ConsumerLattice.dispersive` applies it (ℓ¹ → ℓ^∞ bound). |
| SH, T6L | `ConsumerLattice.not_faster` applies them through `latticeLaplacian_sharp`. |

`OscInt/Front/GlobalSanity.lean` discharges every constant's hypotheses on closed data, but only as a hypothesis `h`:
- E = x³−3xy² for GD and GD-C;
- x³+y³, also off-K and shifted, for GD and GD-C;
- x³+y² for GD-F;
- x²+3xy+5y² on U = B(0,2) for GD-N;
- m^{-1/2} for SH;
- the moments g = 1 and e^{ik₁} for T1;
- the diagonal for T6;
- T6+T6L+SH ⇒ no t^{-3/4} bound.

The data are genuine: none of the hypotheses is impossible, and each D4 or fold witness is proved.

My own check, `/tmp/ppB/inst.lean`, compiles at HEAD with no errors. It does the following:
- It instantiates all 13 conditional sanity theorems with the proved theorems: `globalDecay_ell`, `globalDecayCrit_ell`,
  `_hyp`, `_hyp_crit`, `globalDecay_hyp`, `_hyp_offK`, `_hypShift`, `globalFold_fold`, `globalNondeg_quad`,
  `sharpness_sqrt`, `torusUnfold_moments`, `latticeLaplacianDecay_diag` and `latticeLaplacian_sharp`.
- It applies `globalDecayCrit` to x³+y³ with K′ = the closed ball of radius 5 in the dual (an infinite compact set of
  linear terms).

I also compiled a scratch copy of `examples/consumer/ConsumerLattice.lean` (`/tmp/ppB/ConsumerLattice.lean`). It exits
with code 0, and `dispersive` and `not_faster` depend only on the three standard axioms.

## 4. Findings

**BLOCKER:** none. **MAJOR:** none.

**MINOR**
1. **No record shows the consumer example compiling at the reviewed tree.** The record named for batch GD
   (`docs/replay/2026-11-08-session6-GD-verify-all.txt`) contains no step that compiles
   `examples/consumer/ConsumerLattice.lean`, and no file under `docs/replay/` mentions it. The claim that it was
   "compiled in make quick" rests on the c62a621 commit message. Yet README.md:32, CHANGELOG.md:24 and
   ROADMAP.md:57,114 cite it as evidence. I compiled it at c98f496 (scratch copy): it passes. Suggested fix: record a
   `make quick` run, or add the consumer to verify-all.
   - Related gap: the proved GD-C, GD-F, GD-N and T1 are never applied to the conditional sanity theorems in any
     compiled file (GD, T6, SH and T6L are, as in section 3). Adding one-line instantiations to a consumer file, like
     `/tmp/ppB/inst.lean`, would close this.
2. **docs/ROADMAP.md:114 is broader than what is proved.** It reads "[x] decay for lattice Schrödinger operators on
   ℤ²". What is proved is the kernel bound for the free operator with symbol cos k₁+cos k₂, for t ≥ 1: no potential, no
   other lattice operators. Suggested wording: "the free 2D lattice Laplacian".

**NIT**
- `docs/cookbook.md:17` ("once T6/T6L are proved") and `docs/applications.md:9-12` ("see STATUS for whether they exist
  yet") are stale now that all eight are proved.
- `CHANGELOG.md:17-19` describes the m^{-2/3} result only under the pointwise hypothesis, with "uniformly over a compact
  set of linear terms" attached. That under-describes GD-C, whose hypothesis is on critical points only. It is accurate
  but loose.
- `docs/statements.md:470-471` says the ℓ¹ → ℓ^∞ norm *equals* sup_x |K|/(2π)². `ConsumerLattice.lean` proves only the
  upper bound. Its `propagator` is defined by the kernel and is not proved equal to e^{-itH}; its docstring says
  "defined by its kernel", which is honest. Either word the docs as "is bounded by", or note that the equality is not
  formalised.
- `docs/ROADMAP.md:57`: "applied to the lattice kernel by T6L" should read "applied, with T6L, to the lattice kernel".
- `OscInt/Front/GlobalSanity.lean:442`: deprecation warning for `if_pos` (shown in the replay log). It is harmless.
- `docs/STATUS.md:43-50` correctly says "post-proof review pending". Once the reviews are in, the status can follow the
  evidence. Nothing in STATUS or README overclaims at this commit.
