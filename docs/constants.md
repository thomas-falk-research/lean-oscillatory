> Provenance (2026-11-07, session 4): written by an exploration agent that read the S2.2/S3 proofs (no Lean written
> except `#check` probes), reviewed by the lead. Labels are the agent's; nothing here is evidence for a theorem.
> **Lead's decision (P5):** do not formalise explicit constants along this route yet. The constant it would produce
> (CONJECTURED ~10⁸–10¹² · R² · B^{20–24} · η^{−8.5…−12}) cannot close the downstream 20-orders gap; the next step is
> the cheap first deliverable of §4 (explicit local theorems for L6 and L1) or a sharper route, which is an owner
> decision (`docs/HANDOFF.md`).

# Explicit constants for S2.2 and S3 (draft for docs/constants.md)

Status: exploration draft, 2026-11-07. Read-only survey of the proof as it stands (`OscInt/StationaryPhase/`,
route `docs/proof-S2S3.md`, interfaces `Blueprint/StationaryPhase.lean`). No Lean was written except a `#check` of
the Mathlib names used below (scratch, outside the tree). Labels: PROVEN (machine-checked in the repo),
VALIDATED (checked here by reading the Lean source or `#check` at the pin), PLAUSIBLE (argued, not checked),
CONJECTURED (an estimate or a design guess).

Goal (ROADMAP §2, downstream's first priority): versions of S2.2 (`StationaryPhaseStatement`, |I| ≤ C·M/m) and S3
(`FoldStatement`, |I| ≤ C·M·m^{-5/6}) in which C is an explicit function of (i) C^k bounds of the phase near the
support, (ii) a gradient / Hessian / fold margin, (iii) M, (iv) the size of K.

## 0. Summary

1. The S2.2 and S3 proofs share one chain (`Final.lean`): `stationaryPhase_of` / `fold_of` (Assembly) ←
   `localization` (R2) ← `localNonCrit` (L1) and `localCrit_of` (L2 `normalForm`, L3–L5 `normalizedData`,
   L6 `coreEstimate`). VALIDATED.
2. The analytic core L6 already has an explicit constant (Core.lean:927, :936). L1's local constant is explicit
   once its radius is (Local.lean:426). VALIDATED.
3. Every non-explicit choice is of one of four kinds: (a) radii from `ContinuousAt` at a point (L1, L3–L5),
   (b) finite subcovers of K and of the parameter space T (R2), (c) a Mathlib partition of unity with no derivative
   control (R2/F2), (d) the passage from the qualitative hypothesis to a margin, which the current proof never makes.
   VALIDATED.
4. Structural recommendation: state the explicit theorems for ONE phase with quantitative hypotheses. Then
   uniformity over Λ and over p ∈ K' is automatic (the constant depends only on the bounds), the cover of the
   parameter space disappears, and the compact topological parameter Λ of S3 (for which no explicit constant can
   exist: nothing quantitative is known about σ ↦ Ψ_σ) is no obstacle. PLAUSIBLE (argued in §1).
5. Make S2.2 explicit first; S3 reuses about 80% of it and needs one new definition (a robust fold margin) that
   needs a statement review. CONJECTURED estimate of the result: C ≈ c₀ · R² · B^{20…24} · η^{-8.5…-12} with an
   absolute c₀ of perhaps 10⁸–10¹². That is finite and checkable but nowhere near sharp. The 20-orders gap that
   downstream reported will NOT close by making this route explicit (§3, §5).

## 1. Dependency structure

### 1.1 The chain as it is (S2.2; S3 differs only where marked)

```
C_final                                    Assembly.lean:105 (S2.2) / :88 (S3)   obtain ⟨C, _⟩ := hLoc (Unit×K' | Λ×K') …
└── R2 localization: C = Σ_{σ∈t_T} C_σ    Localize.lean:125–127   choose over τ₀ ∈ T, elim_nhds_subcover of T
    └── uniform_near τ₀:                   Localize.lean:89–100
        C_σ = Σ_{i∈t_K} |C_i| · Cm_i
        ├── t_K  finite subcover of K by balls(k, δ_k)          Localize.lean:90  elim_finite_subcover
        ├── χ_i  partition of unity                              Localize.lean:96 → Partition.lean:56
        │                                                        SmoothPartitionOfUnity.exists_isSubordinate
        ├── Cm_i = 2²·B_i, B_i = sup_{j≤2} ‖Dʲχ_i‖               Change.lean:104 → :73–80 bddAbove_range_of_hasCompactSupport
        └── C_i  local constant at (τ₀, k_i)  (LocalBound: ∃ U ∃ δ ∃ C, Blueprint:69–73)
            ├── non-critical point (L1)                          Local.lean:409–435
            │   ├── direction e (e₁ or e₂)                       Local.lean:411–413  by_contra!
            │   ├── c = |∂_eQ_{τ₀}(k₀)|/2,  D = ‖D²Q_{τ₀}(k₀)‖+1   Local.lean:417–418  explicit at the point
            │   ├── U × ball(k₀, ε) where |∂_eQ|>c, ‖D²Q‖<D       Local.lean:420–425  mem_nhds_prod_iff, Metric.mem_nhds_iff
            │   └── C = (1/c + D/c²)·vol(closedBall k₀ (ε/2))    Local.lean:426      explicit given ε
            └── critical point (L2–L6)                           LocalCrit.lean:63–84
                C = |det L| · C_core · max(1,‖L‖)²,  δ = min(a,b)/(‖L⁻¹‖+1)     LocalCrit.lean:73–75 explicit given inputs
                ├── L (normal form, L2)                          Local.lean:113–122 (exists_orth_pair), :369–406
                ├── (U, a, b, μ, ν, D) (L3–L5)                   Implicit.lean:500–528 (exists_coreHyps)
                │   ├── r, U₁ from 5 ContinuousAt facts           Implicit.lean:462–488 (exists_nbhd_data), :446–453 (exists_prod_ball)
                │   ├── r', U₂ from continuity of ∂_yQ            Implicit.lean:513–518
                │   ├── b = r/4, a = min(r,r')/4, μ = |q₀|/2, ν = |G(Q_{τ₀})(0)|/2      :510, :519, :523
                │   ├── D = max(b, |Y1(0)|+1, |Y2(0)|+1, Σ_{i≤4}‖DⁱQ_{τ₀}(0)‖+1)        :524–525
                │   └── ys = implicitCurve (Classical.epsilon)    Implicit.lean:148  (unique zero; no constant)
                └── C_core (L6)                                  Core.lean:930–952
                    j=2: 64/(√ν√μ)·Y;  j=3: 144·ν^{-1/3}/√μ·Y
                    Y = (1+4b)(1+2a(1+24β⁶)),  β = max(1, D, 1/μ)          Core.lean:198, :925
                    └── S1.2 / S1.3 constants 8 and 18 (frozen, explicit)
```

### 1.2 Classification of the nodes

| Node | Current status | Explicit version | Class |
|---|---|---|---|
| C_core (L6) | explicit formula (VALIDATED) | change `CoreEstimateFacts` from `∃ C` to the formula | EXPLICIT-EASY |
| L6 dependence on D | D must bound ‖DⁱQ‖ for i ≤ 4, i.e. including the value and gradient of the phase, but `slice_Q_bounds` (Core.lean:562–571) only uses i = 2, 3, 4 (VALIDATED) | restrict `CoreHyps` to i ∈ {2,3,4}. Then C no longer depends on ‖Ψ‖_{C⁰}, ‖∇Ψ‖ or \|p\| | EXPLICIT-EASY |
| L1 constant | explicit given ε, c, D (VALIDATED) | c = λ'/(2√2) from the margin; D = Λ₂; ε = c/Λ₂ by the mean value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le` (VALIDATED name) | EXPLICIT-EASY |
| L1 direction e | `by_contra!` | take the coordinate with the larger \|∂ᵢΦ\| (≥ \|∇Φ\|/√2) | EXPLICIT-EASY |
| L1 neighbourhood U in τ | `ContinuousAt` in τ | S2.2: τ = p and ∂Φ is 1-Lipschitz in p, explicit; S3: σ ∈ Λ has no metric, so no explicit U exists. Removed by the single-phase statement (§4) | NON-CONSTRUCTIVE as stated for S3; removed by the restructure |
| L2 matrix L | explicit, but chosen by exact case tests `h22 = 0`, `h11 = 0` (Local.lean:117–122). When h22 ≠ 0 is tiny, w = e₂, v = (h22, −h12), det L = h22, so ‖L⁻¹‖ ~ 1/h22 is unbounded. VALIDATED | choose w ∈ {e₁, e₂, e₁+e₂, e₁−e₂} maximising \|H(w,w)\| (≥ h := max\|hᵢⱼ\|), v = u − (H(u,w)/H(w,w))·w. Then \|det L\| = 1 and ‖L‖, ‖L⁻¹‖ ≤ small absolute constants | EXPLICIT-EASY (≈150–250 lines) |
| L3–L5 radius r (5 continuity facts) | `eventually_abs_sub_lt` ∘ `ContinuousAt` (Implicit.lean:476–486) | e1: r ≤ q₀/(2Λ̃₃); e2–e4: replace "value at the point + 1" by sup bounds in Λ̃ⱼ and 1/μ (no continuity needed); e5: r ≤ ν/Lip(G), with Lip(G2) ≲ Λ̃₂²Λ̃₃/μ², Lip(G3) ≲ poly(Λ̃₂, Λ̃₃, Λ̃₄)/μ³ by MVT + quotient-rule bounds | EXPLICIT-HARD (bookkeeping; uses only `Convex.norm_image_sub_le_of_norm_fderiv_le`, no missing Mathlib theorem) |
| L3–L5 radius r' | continuity of ∂_yQ at (τ₀, 0) with ∂_yQ(0) = 0 | \|∂_yQ̃(x,0)\| ≤ \|∂_yQ̃(0)\| + Λ̃₃x²/2 (since ∂_x∂_yQ̃(0) = 0). Gives r' ≈ √(q₀b/Λ̃₃) and needs \|∂_yQ̃(0)\| ≤ q₀b/4; this is where the gradient threshold λ_th comes from | EXPLICIT-EASY |
| exact criticality at k₀ | `NormalPoint` asks ∇ = 0; `SliceHyps` only needs \|∂_yQ(x,0)\| < \|c\|b/2 (Implicit.lean:144); G2(0), G3(0) only need ∂_x∂_yQ(0) = 0 (H-orthogonality), not ∇ = 0 | the critical branch works at every k₀ with a small gradient, which turns the dichotomy "critical / not" into "\|∇Φ(k₀)\| < λ_th / ≥ λ_th". PLAUSIBLE | EXPLICIT-EASY |
| implicit curve ys | `Classical.epsilon` of a unique zero; regularity from `ContDiffAt.contDiffAt_implicitFunction` at each point | unchanged: its radius comes from `SliceHyps` (explicit), not from Mathlib's implicit function theorem | no impact |
| finite subcover t_K | `IsCompact.elim_finite_subcover` (Localize.lean:90); size uncontrolled | lattice tiles of side s; their number is ≤ (2R/s + 3)² if K ⊆ closedBall k_c R (max norm); each tile meeting K uses the local bound at a point k₀ ∈ K with radius 2s | EXPLICIT-EASY once a uniform radius s exists |
| partition χ_i | `SmoothPartitionOfUnity.exists_isSubordinate` (Partition.lean:56): no derivative bounds | explicit C² lattice partition: χ_z(x,y) = φ(x/s − z₁)·φ(y/s − z₂), with φ a C² piecewise polynomial (quintic smoothstep) such that Σ_z φ(t − z) = 1; ‖Dʲχ‖ ≤ c_j s^{−j}. `ampBoundMul` only needs χ ∈ Cⁿ (Change.lean:12, VALIDATED) although `AmpBoundMulFacts` asks for C^∞ | EXPLICIT-HARD: Mathlib has no quantitative derivative bounds for bumps (`ContDiffBump`, `Real.smoothTransition`; FiniteDimension.lean:131–139 gets them by `BddAbove`, VALIDATED by grep) |
| Cm_i | `bddAbove_range_of_hasCompactSupport` (Change.lean:77) | Cm = 4·max(1, c₁/s, c₂/s²) | EXPLICIT-EASY given χ |
| T-cover t_T | `IsCompact.elim_nhds_subcover` (Localize.lean:126) over T = Λ × K' | not needed: with uniform local data the per-τ argument gives the same constant for every τ | removed by the restructure |
| margins λ, η (S2.2), η, κ, … (S3) | never formed: the hypothesis is used pointwise at (τ₀, k₀) | explicit theorem takes them as hypotheses. To recover the frozen ∃C statement: min of the continuous positive function (p,k) ↦ max(\|∇Φ_p(k)\|², \|hessDet Ψ k\|) on K'×K (`IsCompact.exists_isMinOn`) gives λ = √m₀, η = m₀. S3: the fold margin needs a continuity or semicontinuity argument (open question) | S2.2: EXPLICIT (an inf functional of the data, not a formula); S3: open |

## 2. Existential choices (table)

Scope: the S2.2/S3 chain only (`NonStat.lean` is S2.1 and not on this chain). "Enters C" = whether the choice
affects the value of the final constant.

| # | File:line | Mechanism | Quantity chosen | Depends on | Enters C | Quantitative replacement (classical?) |
|---|---|---|---|---|---|---|
| 1 | Assembly.lean:105 / :88 | `obtain ⟨C, hCb⟩` from `LocalizationFacts` | final C | everything below | yes | the interface returns a formula |
| 2 | Localize.lean:125 | `choose U hU C …` over τ₀ ∈ T | neighbourhood U_τ₀ and C_τ₀ | the local data at all k ∈ K for this τ₀ | yes | uniform data, no choice (classical) |
| 3 | Localize.lean:126 | `IsCompact.elim_nhds_subcover` on T = Λ × K' | finite t_T ⊆ T, C = Σ_{t_T} C_σ | U_τ₀ | yes (sum, uncontrolled size) | removed (single-phase statement). For S3 with a merely topological Λ, a quantitative version is impossible without new hypotheses on σ ↦ Ψ_σ |
| 4 | Localize.lean:89 | `choose U hU δ hδ C hC` over k ∈ K | U_k, δ_k, C_k (from `LocalBound`) | local analysis at (τ₀, k) | yes | uniform radius s(Λ, margins) and uniform C_loc (classical) |
| 5 | Localize.lean:90 | `IsCompact.elim_finite_subcover` | finite t_K ⊆ K | δ_k | yes (sum, uncontrolled size) | lattice count ≤ (2R/s + 3)² (classical; Lebesgue-number-type argument made explicit by uniform s) |
| 6 | Localize.lean:96, Partition.lean:56 | `SmoothPartitionOfUnity.exists_isSubordinate` | χ_i | t_K, δ_k | yes, through Cm_i | explicit C² lattice partition (classical; not in Mathlib) |
| 7 | Localize.lean:98, Change.lean:104, :73–80 | `choose Cm …`; `bddAbove_range_of_hasCompactSupport` | Cm_i = 4·B_i | χ_i | yes | Cm = 4·max(1, c₁/s, c₂/s²) |
| 8 | Partition.lean:51 | `isBounded.subset_ball` | radius R of a ball containing K | K | no | (harmless) |
| 9 | Local.lean:411–413 | `by_contra!` | coordinate direction e | ∇Q_{τ₀}(k₀) | yes (through c) | larger coordinate of the gradient |
| 10 | Local.lean:420–425 | `mem_nhds_prod_iff`, `Metric.mem_nhds_iff` (Filter → δ) | U, ε (L1) | continuity of ∂_eQ and ‖D²Q‖ at (τ₀, k₀) | yes (vol(ball ε/2), cover size) | ε = c/Λ₂ by the mean value inequality; U in p: Lipschitz 1 (classical) |
| 11 | Local.lean:117–122, :382–383, :392, :400 | `by_cases h22 = 0`, `h11 = 0`; `obtain ⟨v, w, …⟩`, `obtain ⟨L, …⟩` | normal-form matrix L | exact Hessian entries | yes (\|det L\|, ‖L‖, ‖L⁻¹‖) and discontinuously | well-conditioned choice of w (classical: pivoting) |
| 12 | LocalCrit.lean:69 | `obtain ⟨U, hU, a, b, μ, ν, D, …⟩` from `NormalizedDataFacts` | box and bounds | #13–#15 | yes | interface returns formulas |
| 13 | Implicit.lean:446–453, :462–488 | `exists_prod_ball` (`eventually_prod_iff`, `Metric.eventually_nhds_iff`) on five `ContinuousAt` facts | U₁, r | continuity at (τ₀, 0) of ∂²_yQ, Σ‖DⁱQ‖, Y1, Y2, G2/G3 | yes (a, b, D, cover size) | Lipschitz bounds by MVT from Λ₂..Λ₄ and 1/μ (classical; bookkeeping heavy) |
| 14 | Implicit.lean:513–518 | `exists_prod_ball` on continuity of ∂_yQ | U₂, r' | ∂_yQ(τ₀, 0) = 0 | yes (a) | Taylor: \|∂_yQ̃(x,0)\| ≤ \|∂_yQ̃(0)\| + Λ̃₃x²/2 |
| 15 | Implicit.lean:524–525 | explicit `max` | D = max(b, \|Y1(0)\|+1, \|Y2(0)\|+1, Σ_{i≤4}‖DⁱQ(0)‖+1) | values at the point, including \|Q(0)\| and \|∇Q(0)\| | yes (β⁶) | drop i = 0, 1 (unused by L6) and the Y-bounds (unused by L6, Core.lean:25) |
| 16 | Implicit.lean:148 | `Classical.epsilon` | implicit curve ys | unique zero of ∂_yQ(x, ·) | no | none needed |
| 17 | Implicit.lean:187, Core.lean:163 | `by_contra` | (uniqueness / IVT steps) | — | no | none needed |
| 18 | Core.lean:111, :691 | `IsCompact.exists_bound_of_continuousOn` | dominating bound for differentiation under ∫ | — | no (only integrability) | none needed |
| 19 | LocalCrit.lean:70 | `obtain ⟨C, hC⟩` from `CoreEstimateFacts` | C_core | (j, a, b, μ, ν, D) | yes | already a formula (Core.lean:927, :936) |
| 20 | Assembly.lean:105–111 / :88–93 | qualitative hypothesis used pointwise; no margin | — | — | implicitly (radii at every point) | margin hypotheses; recovering the frozen statement needs `IsCompact.exists_isMinOn` (S2.2) |

Not found on this chain (VALIDATED by grep and reading): Lebesgue number lemmas, uniform continuity
(`CompactSpace.uniformContinuous_of_continuous`), `exists_forall_le`, contraction / Banach fixed point (the route's
contraction was replaced by the intermediate value theorem, Implicit.lean:22). `generalized_tube_lemma` is used
only in `NonStat.lean:468` (S2.1).

## 3. Shape of the constant

Everything in this section is CONJECTURED (hand estimates, absolute constants not tracked carefully).

Data (one phase Φ = Ψ + p·, max norm on ℝ² as in the repo):
- Λⱼ ≥ sup ‖DʲΨ‖ on K_ρ = K + closedBall 0 ρ, j = 2, 3, 4; B := max(1, Λ₂, Λ₃, Λ₄). Λ₁, ‖Ψ‖_{C⁰} and \|p\| are NOT
  needed once item 15 is fixed (p only shifts ∇Φ).
- K ⊆ closedBall k_c R; amplitude bound (2, K, M).
- S2.2 margin: for every k ∈ K, \|∇Φ(k)\| ≥ λ or \|hessDet Ψ k\| ≥ η (η ≤ 2Λ₂² automatically).
- S3 margin: for every k ∈ K, \|hessDet\| ≥ η or a fold margin (κ: third derivative along the near-kernel
  direction; η₂: the nonzero eigenvalue); no λ in the hypothesis (S3's condition is independent of p), λ_th is
  internal.

Derived scales (S2.2):
- h = max\|hᵢⱼ\| ≥ √(η/2); well-conditioned L: \|det L\| = 1, ‖L‖, ‖L⁻¹‖ ≤ 5, Λ̃ⱼ ≤ 5ʲΛⱼ.
- μ ≈ h/2, ν = \|G2(0)\|/2 ≥ η/(8h) (G2(0) = H(v,v) = det H·det(L)²/H(w,w)).
- Box radius r ≈ min(h/Λ̃₃, ν μ²/(Λ̃₂²Λ̃₃)) ≳ c·η^{3/2}/(Λ₂²Λ₃); a ≈ b ≈ r/4.
- Gradient threshold λ_th ≈ q₀ b/(4‖L‖) ≳ c·√η·r; λ' = min(λ, λ_th).
- L1 radius ε ≈ λ'/(3Λ₂); local L1 constant (1/c + Λ₂/c²)·ε² ≈ 2/Λ₂ (bounded: the ball's area cancels 1/c²).
- Local critical constant C_crit ≈ 25·64·(νμ)^{-1/2}·(1 + 4b)(1 + 2a(1 + 24β⁶)) ≈ 6400·η^{-1/2}(1 + 12 r β⁶),
  β = max(1, 625·B, 2/h).
- Tile side s ≈ min(ε, δ_crit)/2 ≈ λ'/(6Λ₂); count N ≤ (2R/s + 3)²; cut-off cost Cm ≈ 4c₂/s².

Total:

  C_S2.2 ≈ (2R/s + 3)² · (4c₂/s²) · max(2/Λ₂, 6400·η^{-1/2}(1 + 12 r β⁶)),   s ≈ min(λ, c√η·r)/(6Λ₂).

For a large gradient margin (λ ≥ λ_th) and R ≥ s this is about

  C_S2.2 ≈ c₀ · R² · Λ₂^{12} Λ₃⁴ · η^{-8.5} · (1 + r·β⁶),

so C ≈ c₀ · R² · B^{~20…24} · η^{~-8.5…-12} (the exponent of η grows if 1/μ dominates β). Even for B = R = η = 1, the
absolute constant c₀ is plausibly 10⁸–10¹² (6400 · 25 · c₂ · 6⁴ · 3² · …).

S3 (rate 5/6): the same with C_core,3 = 144·ν₃^{-1/3}/√μ·Y, ν₃ ≈ κ/2·(‖L‖-dependent factor), r_fold ≈ ν₃/Lip(G3)
with Lip(G3) ≈ poly(Λ̃₂, Λ̃₃, Λ̃₄)/μ³. Expected C_S3 ≈ c₀' · R² · B^{~25…30} · η^{-~9} · κ^{-~5} · η₂^{-~6}.

Where the size comes from (PLAUSIBLE): (i) the factor s^{-2} in Cm. The single-M `AmpBound` interface charges every
tile the full C² norm of χA, so a localisation at scale s costs s^{-2} even where the local estimate only uses M₀
and M₁; (ii) the tile count (R/s)²; (iii) β⁶ from the core estimate (`1 + 24β⁶`, Core.lean:21, :925); (iv) the
nested worst cases (s is set by the smallest radius anywhere). The true size is about 2π·\|det\|^{-1/2}·M per
critical point (leading term of stationary phase), so the route's constant is likely 10¹⁰ or more times too large on
benign data. That is the same kind of gap downstream reported.

## 4. Recommendation

1. Order: S2.2 first. It has no topological parameter, its margin is the simple pair (λ, η), only the j = 2
   branch is needed, and the parameter p enters with Lipschitz constant 1 and not at all beyond first derivatives.
   It builds all the shared infrastructure: the quantitative L1, the well-conditioned normal form, the explicit
   radii for e1–e4 and G2, the lattice partition and the tile count. S3 then adds the fold margin definition, the
   G3 Lipschitz bound (uses Λ₄) and the vdc3 branch.
2. Statement shape. One phase, no Λ and no K':
   ```
   ∀ Ψ K A M p m (Λ₂ Λ₃ Λ₄ η lam R ρ : ℝ) (k_c : ℝ × ℝ),
     ContDiff ℝ 4 Ψ → K ⊆ closedBall k_c R → 0 < η → 0 < lam → 0 < ρ →
     (∀ k, infDist k K ≤ ρ → ∀ j ∈ {2,3,4}, ‖iteratedFDeriv ℝ j Ψ k‖ ≤ Λⱼ) →
     (∀ k ∈ K, GradLower Ψ p k lam ∨ η ≤ |hessDet Ψ k|) →
     AmpBound 2 K A M → 1 ≤ m →
     ‖oscInt2 (fun k => m * (Ψ k + lin p k)) A‖ ≤ spConst Λ₂ Λ₃ Λ₄ η lam R ρ * M / m
   ```
   with `spConst` an explicit `noncomputable def` in the statement file, built from `max`, `+`, `*`, `/` and
   `Real.sqrt` (avoid `rpow`: η^{3/2} = η·√η), monotone in each argument, and stated with B = max 1 … so that it
   is total. Prefer `≤ f(…)` with a defined `f` over `∃ C ≤ f(…)`: the two are equivalent when M ≥ 0, but the first is
   what a downstream user evaluates (`norm_num`, interval arithmetic) and what a faithfulness referee can read.
   Make f a deliberately simple monomial upper bound (e.g. c₀·(1 + R/s)²·s^{-2}·η^{-1/2}·B⁶ with s a monomial in
   λ, η, B) and prove the messy bound ≤ f in the proof; then the frozen formula is short. Uniformity over
   compact families (the ROADMAP's "parametric uniformity" item for S2.2) and over p follows by quantifying, and
   the frozen S2.2/S3 follow by a compactness argument for the margins (bridge theorems, cheap). Add sanity
   theorems per lesson 17 (generic data, a "bite" case where the margin fails) and a `norm_num` evaluation of f on a
   sample.
   Correction (2026-11-14): this sketch first used `λ` as a binder name; `λ` is a Lean keyword, and the R4 packet
   copied the error into its draft (`review/2026-11-14-external-R4-answers.md`). The binder is now `lam`.
3. Interfaces to change (blueprint): `LocalBound` → a quantitative `LocalBoundAt (δ C)`; `CoreEstimateFacts` →
   formula; `NormalizedDataFacts` → (a, b, μ, ν, D) as formulas in (Λ̃, q₀, G(0)); `NormalFormFacts` → bounds on
   ‖L‖, ‖L⁻¹‖, |det L|; `PartitionFacts` → lattice partition with derivative bounds; `CoreHyps` → drop i = 0, 1 and
   the ys-bounds. Each a new blueprint Prop; the frozen statements are untouched.
4. Size (CONJECTURED, compared with the current ≈ 2 900 lines of `OscInt/StationaryPhase/` on the S2.2/S3 chain, i.e. excluding `NonStat.lean` and `Sanity.lean`): S2.2-explicit 1 800–2 700
   new lines: lattice C² partition with bounds 400–600; quantitative L3–L5 radii (MVT + quotient bounds for Y1,
   Y2, G2) 400–700; well-conditioned normal form 150–250; quantitative L1 80–150; tile localisation and lattice
   count 200–300; arithmetic to the monomial f 200–400; statement, sanity, bridges 150–250. S3 increment: 600–1 000
   (fold margin, G3 Lipschitz, vdc3 branch, margin bridge). The core L6 (946 lines) is reused with an interface
   change of about 30 lines.
5. Mathlib gaps (VALIDATED by `#check` and grep at the pin): no quantitative derivative bounds for bump functions or
   partitions of unity (`ContDiffBump`, `Real.smoothTransition`, `SmoothPartitionOfUnity` give existence only), so
   write the piecewise polynomial C² bump by hand. No quantitative implicit function theorem is needed (the IVT
   route gives the radius explicitly). The mean value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le`
   exists. Lattice-point counting in a box is elementary (`Finset.Icc` on ℤ²). No Lebesgue number or uniform
   continuity lemma is needed.
6. Expectation management, before anyone formalises: tell downstream that the explicit constant from this route
   will be astronomically pessimistic (§3), so it detects qualitative failures, not quantitative fit. If they need
   constants within an order or two of observation, the right object is different: the leading-term asymptotics
   (ROADMAP "asymptotic expansions") with an explicit remainder, or a scale-aware amplitude norm (M₀, M₁, M₂ and
   support area separately) that removes the s^{-2} loss. A cheap first deliverable that already has value: make
   L6 (core) and L1 explicit as standalone local theorems on a box. Their constants are moderate
   (64(νμ)^{-1/2}·Y and ≈ 2/Λ₂ per tile), and a user who can localise by hand gets usable numbers.

## 5. Open questions

1. Robust fold margin for S3 (needs design and a blind statement review). Candidate: at each k ∈ K,
   \|hessDet Ψ_k\| ≥ η, or (‖D²Ψ(k)‖ ≥ η₂ and |D³Ψ(k)[v,v,v]| ≥ κ for every unit v with ‖D²Ψ(k)v‖ ≤ θ). Is it
   implied by `FoldOrNondeg` on compact K with some η, η₂, κ, θ > 0 (by contradiction / sequences; the near-kernel
   condition is only semicontinuous)? Which formulation keeps the canonical v of the normal form inside the margin?
2. Does the critical branch really need only a small gradient at k₀ (§1.2, "exact criticality")? PLAUSIBLE from
   reading `SliceHyps` and the G2/G3 formulas; to be confirmed by a short paper argument before the blueprint.
3. Sharpness of the framework loss: how much of c₀·s^{-4} disappears with a scale-aware amplitude bound? Would
   downstream accept a new amplitude hypothesis (separate M₀, M₁, M₂)? This changes the statement, not just the proof.
4. Should the explicit statement keep `p` and S2.2's "only at critical points" form, or adopt S3's "at every
   point of K" form? The margin (λ, η) form above covers both, but its relation to the frozen hypothesis must be
   written down (bridge lemma).
5. Domain of the C^k bounds: on K_ρ (as proposed) or on all of ℝ²? K_ρ matches the ROADMAP "local smoothness" item
   and costs one more parameter ρ (s ≤ ρ).
6. Numerics: the repo's `numerics/` can measure |I|·m/M on sample phases (saddle, fold, the S4 cubics) to show
   downstream the gap between c₀(…) and observation before the formalisation starts. Recommended as a pre-registered
   experiment.
7. Absolute constants: should the frozen f carry round numbers (10¹², say) with slack, or tracked ones? Slack makes
   the proof shorter and the review easier; tracked constants make it more useful. Suggest slack, a factor ≤ 10 per
   step, with the exact tracked expression documented as CONJECTURED next to it.
