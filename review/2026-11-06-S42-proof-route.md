<!-- Route referee for S4.2 (fresh-context agent, prompt review/prompts/S42-proof-route.md), commit 43db070. Verbatim final report. -->

`43db070454a6fa454410cc08ea1bc7f357bb74d5`

# Referee report: S4.2 proof route (`docs/proof-S42.md`) and blueprint E1–E3 (`Blueprint/D4LimitS42.lean`), commit 43db070

I read the files the brief names at 43db070 and, for the F1c/F1d/F2b signatures only, `Blueprint/StationaryPhase.lean`. I read no proof file, compiled nothing and wrote nothing in the repository. I checked the Mathlib names in `.lake/packages/mathlib`. One scratch numeric check, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/c.py`, confirms the radial lemma: λ^{2/3}∫cos(λr³)ψ(r)r dr → Γ(2/3)/6 = cosMoment/3 to 10 digits at λ = 100.

**Verdict: yes, E1–E3 can go to proof agents as they stand.** All three are TRUE as stated in Lean, and the route is correct mathematics. There is no BLOCKER. Before the *assembly* can be written, add the piece bound as an explicit part (MAJOR 1). I recommend splitting E1 and proving it by a cleaner 1D argument (MINOR 2–3).

## 1. The route, step by step

- **Step 0: correct.** Symmetrising χ ↦ (χ + χ(−·))/2 keeps every D7 property:
  - values in [0, 1];
  - χ = 1 on B̄(0, 1) and tsupport ⊆ B̄(0, 2), because both balls are symmetric;
  - χ(2z) ≤ χ(z), by adding the inequalities at z and −z.

  β = χ − χ(2·) is 0 for ‖z‖ < 1/2 and for ‖z‖ > 2, so tsupport β ⊆ 𝒜. With y = 0 and ∇φ(0) = 0 the rescaled linear term is p = 0 ∈ B̄(0, 1), so only S3 is needed and not S2.1. F1d with L = ε·id and ε ≤ 1 gives the factor max(1, ε)² = 1.
- **Step 1: correct.** β(κ/ε_j) = χ(κ/ε_j) − χ(κ/ε_{j−1}), so the sum telescopes to χ(κ/(2^Nρ)) − χ(κ/ρ). Also χ(κ/(2^Nρ)) = 1 for ‖κ‖ ≤ δ ≤ 2^Nρ. Since tsupport A ⊆ B̄(0, δ), the identity A = χ(·/ρ)A + Σ β(·/ε_j)A holds everywhere. N = 0 (no outer pieces) is harmless.
- **Step 2: correct.**
  - Minimality of N gives 2^{N−1}ρ < δ, so ε_j ≤ 2^Nρ < 2δ = ε₀ for N ≥ 1.
  - tε_j³ = 2^{3j}R³ ≥ 1.
  - Each term is ε_j²(tε_j³)^{−5/6} = 2^{−j/2}R^{−1/2}t^{−2/3}. Their sum is at most 1/(√2−1) ≈ 2.414 ≤ 3, uniformly in t > 0.
  - The amplitude bound on B̄(0, δ) implies the bound on B̄(0, ε₀).
- **Step 3: correct.** With s = t^{−1/3} we have ts³ = 1, and t·φ(s•w) = rescale φ s w for s ≠ 0. Also ρ⁻¹•(s•w) = R⁻¹•w and t^{2/3}·s² = 1. The limit is dominated convergence. In Lean, s → 0 comes from `tendsto_rpow_neg_atTop`, and continuity of (s, w) ↦ Ψ_s(w) is the j = 0 case of D2.
- **Step 4: correct.**
  - **Evenness:** C(−w) = −C(w) and χ is real and even, so w ↦ −w gives L = conj L.
  - **Polar substitution:** with r dr = (1/3)|g|^{−2/3}u^{−1/3}du the formula is right, and cos is even in g.
  - **Max norm:** ‖rω‖_max ≤ r gives ψ_θ = 1 on [0, 1]. ‖rω‖_max ≥ r/√2 gives a θ-uniform outer radius.
  - **Uniform-in-θ bound:** it holds because B and K do not depend on θ.
  - **Dominated convergence in θ:** the bound is const·|g|^{−2/3}, integrable by S4.3. Pointwise convergence uses Λ = |g|R³ → ∞ where g ≠ 0. The zeros of g form a null set (see MINOR 3).
  - **Angular range:** ∫_{−π}^{π} = ∫₀^{2π} by `Function.Periodic.intervalIntegral_add_eq`, and integrability transfers by `Function.Periodic.intervalIntegrable`.
  - Inaccuracies in the text: MINOR 2 and NIT 5.
- **Step 5: correct.** The outer bound times t^{2/3} is 3C₃C_βM·R^{−1/2} for every t > 0. So the order (R first, then t₀(R)) is legitimate. Constant signs: NIT 7.

## 2. E1–E3 in Lean

- **E3 is TRUE.** The parenthesisation is (t·ε³)^{−5/6} with ε = 2^{j+1}(R·t^{−1/3}). All bases are positive, and (t^{−1/3})³ = t^{−1} for t > 0. N can be any index with 2^{N−1}ρ < δ ≤ 2^Nρ, or N = 0 when ρ ≥ δ. The hypothesis `1 ≤ R` is unused.
- **E2 is TRUE, including along `𝓝 0`** (both signs of s, and s = 0 itself).
  - Each integrand is continuous, hence measurable.
  - A dominating function: sup‖B‖ · sup{‖A(s•w)‖ : |s| ≤ 1, w ∈ tsupport B}, which is finite by compactness, times the indicator of tsupport B.
  - Pointwise convergence follows from joint continuity. Then `integral_mul_const`.
  - The use only needs `𝓝[>] 0`, which this implies.
- **E1 is TRUE.**
  - At R = 0, `R⁻¹ • w = 0`. This is irrelevant along `atTop`.
  - Only `HasCompactSupport χ` is assumed (no `tsupport ⊆ B̄(0,2)`, no values in [0, 1]). The proof then uses a generic support radius K₀ and sup|χ|, which is fine.
  - The coercions `((χ (R⁻¹ • w) : ℝ) : ℂ)` and `((d4Constant q : ℝ) : ℂ)` are fine.
  - The `circleCubic` in the hypothesis is definitionally the integrand of `angularMoment`.
  - Evenness is not strictly needed for the limit, because the sine part cancels by g(θ+π) = −g(θ). It does simplify the proof.
- **Sufficiency.** With S4.3 used through `D4ConstantPosStatement`, E1–E3 give the analytic steps. But the assembly also needs the following, and **the first item is not available as a part**:
  - the piece bound (MAJOR 1);
  - D2, D3, D4, D5, D7 and F1c, F1d, F2b, with `OscInt.fold` for that bound;
  - finite-sum integrability (continuous compactly supported integrands);
  - `cubicPoly = cubicForm` (NIT 6).

  I see nothing else that cannot be assembled.

## Findings

**MAJOR 1: the piece bound is not a blueprint part.**
- Exact text: "**Piece bound** (from the S4.1′ assembly, with linear term 0): … |∫ e^{itφ} β(·/ε) A| ≤ C₃ C_β M ε² (tε³)^{−5/6}".
- In the S4.1′ route this bound lives inside the assembly proof, and only for ε = ε₀/2^j and the D7 χ chosen there. S4.2 needs it for:
  - arbitrary ε ∈ (0, ε₀];
  - the *symmetrised* χ, which must be the same χ as in the inner piece and E1.
- The route does not name it as a lemma. Unless the S4.1′ development exposes exactly this, the assembly has to redo the S3, F1c, F1d, F2b and gauge argument. Suggested part E0, stated with ε₀ before χ, which is legitimate because ε₀ comes from the gauge and depends only on φ:

```lean
def PieceBoundFacts : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ → φ 0 = 0 → fderiv ℝ φ 0 = 0 → (∀ v w, dd φ 0 v w = 0) →
    disc (cubicCoeffs φ) ≠ 0 → ∃ ε₀ > 0, ε₀ ≤ 1 ∧
      ∀ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ → (∀ z, ‖z‖ ≤ 1 → χ z = 1) → tsupport χ ⊆ Metric.closedBall 0 2 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ × ℝ → ℂ) (M ε t : ℝ), AmpBound 2 (Metric.closedBall 0 ε₀) A M →
          0 < ε → ε ≤ ε₀ → 1 ≤ t * ε ^ 3 →
            ‖oscInt2 (fun κ => t * φ κ)
                (fun κ => ((χ (ε⁻¹ • κ) - χ ((2 : ℝ) • ε⁻¹ • κ) : ℝ) : ℂ) * A κ)‖ ≤
              C * M * ε ^ 2 * (t * ε ^ 3) ^ (-(5 : ℝ) / 6)
```

**MINOR 2: E1's 1D lemma uses facts outside E1's hypotheses, and the text misdescribes C1.**
- Exact text: "for Λ ≥ 1 by one integration by parts (C1 of S4.3) … tends to (1/3)S = cosMoment".
- C1 is the integration by parts *without* η. The one with η(u/Λ) is new.
- Identifying (1/3)∫₀^∞ sin u·u^{−4/3} with `cosMoment` needs C1 and C2 (with S), which E1 does not assume. The route also needs:
  - the cube-root amplitude η_θ(v) = ψ_θ(v^{1/3}), whose derivative is singular at 0;
  - a case split Λ ≤ 1 versus Λ ≥ 1.
- Recommended replacement, using only E1's hypotheses and avoiding the cube root. Write ψ_θ(r) = χ(r·ω(θ)), which is C^∞ in r, with |ψ_θ′| ≤ sup‖Dχ‖ and ψ_θ = 0 for r ≥ K = √2·K₀. By ψ(r) = −∫_r^K ψ′, Fubini, and the substitution u = λr³ on [0, ρ]:

  λ^{2/3} ∫₀^K cos(λr³) ψ(r) r dr = −(1/3) ∫₁^K ψ′(ρ) · cosMomentPartial(λρ³) dρ.

  Since cosMomentPartial is continuous and convergent, it is bounded on [0, ∞). This gives a bound uniform in λ > 0 and θ, and the limit (1/3)·cosMoment·(ψ(1) − ψ(K)) = cosMoment/3 by dominated convergence. The numeric check above confirms the limit.
- The substitution works with `intervalIntegral.integral_comp_mul_deriv'''`. It needs g(u) = cos u·u^{−1/3} continuous only on the open image (0, λρ³).

**MINOR 3: null set of zeros.**
- Exact text: "the zeros of g are finitely many, a null set".
- This is true (Disc ≠ 0 implies q ≠ 0, so a·x³ + b·x² + c·x + d is a nonzero polynomial). But it is neither in E1's hypotheses nor a part. Either:
  - add C3's conclusion `∀ θ, circleCubic q θ = 0 → deriv (circleCubic q) θ ≠ 0` as a hypothesis of E1: zeros are then isolated, hence finite on [−π, π], hence null; or
  - make it a sub-part (E1c below).

**MINOR 4: E3 omits tε³ ≥ 1.**
- The piece bound needs `1 ≤ t * ε_{j+1}^3`. The assembly must then redo the rpow computation that E3's proof already does.
- Add `∀ j < N, 1 ≤ t * (2 ^ (j + 1) * (R * t ^ (-(1:ℝ)/3))) ^ 3` to E3. It is true from R ≥ 1, which makes that hypothesis useful.

**NIT 5.** Exact text: "η_θ = 0 on [(2√2)³, ∞)". This assumes tsupport χ ⊆ B̄(0, 2), but E1 assumes only `HasCompactSupport χ`. The proof must use a generic radius.

**NIT 6.** `rescale φ 0 = cubicPoly (cubicCoeffs φ)` (Blueprint.D4), while E1 uses `cubicForm`. These are separate definitions with the same body, so a `rfl`/`funext` bridge is needed in the assembly.

**NIT 7.** Exact text: "≤ 3 C₃ C_β M R^{−1/2} t^{−2/3}". Multiplying the E3 sum by C₃C_βM needs C₃C_βM ≥ 0. M ≥ 0 follows from `AmpBound`, but C₃ from S3 may be negative. Use max(C₃, 0), as the S4.1′ route does (D = max(…)), or require `0 ≤ C` in E0.

**NIT 8.** Exact text: "Σ_{j≥1} 2^{−j/2} ≤ 3". The true value is 1 + √2 ≈ 2.414, so this is fine, just loose.

## 3. E1: size, Mathlib obstacles, split

**Size:** roughly 800–1300 Lean lines in total. Too large for one agent; I suggest four parts.

- **E1a: radial identity, ~200–300 lines.** For ψ : ℝ → ℝ C¹, 1 ≤ K, ψ = 1 on Icc 0 1, ψ = 0 on [K, ∞), and λ > 0:
  `λ^(2/3) * ∫ r in 0..K, cos(λ r³) ψ r r = -(1/3) ∫ ρ in 1..K, deriv ψ ρ * cosMomentPartial (λ ρ³)`.
  Tools: FTC, interval Fubini, `integral_comp_mul_deriv'''`, rpow algebra.
- **E1b: polar reduction, ~250–400 lines.** For R > 0:
  `oscInt2 (cubicForm q) (χ(R⁻¹•·)) = ((∫ θ in -π..π, ∫ r in 0..K', r cos(r³ g θ) χ(R⁻¹ • (r cos θ, r sin θ))) : ℂ)`.
  Tools:
  - evenness via `integral_neg_eq_self` and `integral_conj`;
  - `integral_comp_polarCoord_symm` (target is `Ioi 0 ×ˢ Ioo (-π) π`);
  - `setIntegral_prod` with the order swapped so θ is outer;
  - integrability of r·f(polarCoord.symm p) on the target, which is continuous with bounded support. This is the fiddly bit.
- **E1c: zeros null, ~80–200 lines.** `disc q ≠ 0 → volume {θ | circleCubic q θ = 0} = 0`. Use C3 with `HasDerivAt.eventually_ne` and finiteness on a compact set, or the polynomial-in-cot θ argument.
- **E1d: combine, ~250–400 lines.**
  - Scale r = Rρ.
  - Use R²(|g|R³)^{−2/3} = |g|^{−2/3} (`Real.mul_rpow`, `Real.rpow_natCast`).
  - Bound sup|ψ_θ′| ≤ sup‖fderiv χ‖ uniformly in θ.
  - Apply `tendsto_integral_filter_of_dominated_convergence` along `atTop` on ℝ (countably generated), with the ae limit off the E1c null set.
  - Shift [−π, π] to [0, 2π] by periodicity (`Function.Periodic.intervalIntegral_add_eq`, `.intervalIntegrable`).

**Other Mathlib pain points:**
- interval versus set integrals on `Ioo (-π) π` (`integral_Ioc_eq_integral_Ioo`, `intervalIntegral.integral_of_le`);
- `AEStronglyMeasurable` of θ ↦ inner integral, from `Integrable.integral_prod_left`;
- getting continuity of `cosMomentPartial` on [0, ∞) from local integrability of u^{−1/3}, needed for the bound in E1a/E1d.