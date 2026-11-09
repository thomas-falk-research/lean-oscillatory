# Route: batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

Lead, 2026-11-09, after the pre-proof reviews were committed and stamped (`stamps/20261109T002419Z-45505299011a`).
Blueprint: `Blueprint/Vector.lean` (`VecTransferFacts`). Assembly: `OscInt/Front/VectorAssembly.lean` (the four statements
from the proved scalar statements of batch GD and P-transfer, with `θ = m(Ψ + L)` and the scalar constant; compiled
before the part). Names checked at the pin by both pre-proof referees; those used are in `MathlibNames.lean`.

## The part P-transfer (`VecTransferFacts`), proved as a universe-polymorphic theorem
Given `K` compact, `U ⊇ K` open, `θ` continuous on `U`, a bound `B M` for every scalar amplitude `(2, K, M)`, and an
`E`-valued amplitude `A` `(2, K, M)`:
1. `f k = e^{iθ(k)} • A(k)` is continuous (at `k ∉ tsupport A`, `f` vanishes on a neighbourhood: `notMem_tsupport_iff_eventuallyEq`;
   at `k ∈ tsupport A ⊆ U`, `θ` is continuous at `k`, `U` open) with `HasCompactSupport` (inside `K`), so integrable
   (`Continuous.integrable_of_hasCompactSupport`).
2. `v = ∫ f`; Hahn–Banach `exists_dual_vector'' ℂ v`: `ℓ`, `‖ℓ‖ ≤ 1`, `ℓ v = ‖v‖`.
3. `ℓ v = ∫ ℓ (f k)` (`ContinuousLinearMap.integral_comp_comm`, step 1) `= ∫ e^{iθ(k)} * ℓ (A k)` (`map_smul`, `smul_eq_mul`).
4. `ℓ ∘ A` is a scalar amplitude `(2, K, M)`: `ContDiff` (composition with `ℓ.restrictScalars ℝ`), `tsupport` (`tsupport_comp_subset`, `ℓ 0 = 0`),
   `‖D^j(ℓ ∘ A)‖ ≤ ‖ℓ.restrictScalars ℝ‖ ‖D^j A‖ ≤ M` (`ContinuousLinearMap.norm_iteratedFDeriv_comp_left`,
   `ContinuousLinearMap.norm_restrictScalars`, `M ≥ 0` from the `j = 0` bound).
5. `‖v‖ = ‖(‖v‖ : ℂ)‖ = ‖ℓ v‖ ≤ B M` by the scalar bound.

## Revision after the route referee (`review/2026-11-09-VT-route-referee.md`, at 52188e4)
Verdict: no BLOCKER, no MAJOR; `VecTransferFacts` true (edge cases E = 0, M < 0, K empty, θ off U, B arbitrary checked);
every name fits in the blueprint's instance context; the assembly proves exactly the frozen statements. This revision
and the report are committed **before** the part's proof enters the repository (lessons 42; the lead's draft was kept in
the session scratchpad while the referee ran).
- **M1 (names not all in `MathlibNames.lean`).** Fixed: `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`,
  `tsupport_comp_subset`, `notMem_tsupport_iff_eventuallyEq`, `Continuous.integrable_of_hasCompactSupport`,
  `HasCompactSupport.intro`, `image_eq_zero_of_notMem_tsupport` added.
- **M2 (assembly not in the default build).** It becomes built and audited when `OscInt/Front/VectorFinal.lean` imports
  it (with the proofs); until then "compiles" is the lead's and the referee's manual check.
- **M3 (numeric interface check).** Not applicable: a pure duality transfer has no quantity to measure.
- **N1–N4.** Step 1 uses `HasCompactSupport.intro` (ℝ² is R1) and pointwise continuity (`continuous_iff_continuousAt`,
  `ContinuousAt.congr`, `ContinuousOn.continuousAt` with `IsOpen.mem_nhds`); step 4's `M ≥ 0` is not needed but kept in
  the draft; step 5 by `simp` on `‖(‖v‖ : ℂ)‖`; the delivered constant is `vecTransfer : VecTransferFacts`, a one-line
  application of the universe-polymorphic `transfer`.
