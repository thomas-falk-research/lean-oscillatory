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
