> Provenance (2026-11-07, session 4): design document (P9a) written by an exploration agent and reviewed by the lead;
> draft statements elaborate against `import OscInt.Statements.D4Limit` but are NOT frozen statements and have no
> proofs. The lead re-checked §1.4's key claim (the Hessian determinant of a periodic phase integrates to zero, so
> σ = 1 holds only in a cone of velocities): θ_xxθ_yy − θ_xy² = ∂_x(θ_xθ_yy) − ∂_y(θ_xθ_xy). Numerics cited are tooling,
> never evidence. Scratch files named in the text are not in the repository.

# Design: torus and lattice kernels (OscInt, ROADMAP §5 "periodic and lattice settings")

Status of this document: DESIGN ONLY. No statement here is stamped, frozen or reviewed, and no proof exists.
Written 2026-11-07 against the repository at its working tree (toolchain v4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`). Nothing in the repository was edited.

Labels: **PROVEN** (a complete argument is given here or is a standard textbook fact with the argument sketched),
**VALIDATED** (machine-checked: Lean elaboration, `#check`, or floating-point numerics, which in this repository are
tooling and never evidence), **PLAUSIBLE** (a route that looks right but was not checked in detail),
**CONJECTURED** (believed, with partial evidence only), **OPEN**.

Companion files (scratch, not in the repository):

| File | Content |
|---|---|
| `docs/design/torus-lattice/TorusDraft.lean.txt` | every draft `def …Statement : Prop` below; **elaborates without error** against `import OscInt.Statements.D4Limit` (VALIDATED, `lake env lean`, 2026-11-07), plus a closed proof that the lattice Laplacian is `Periodic2` |
| `docs/design/torus-lattice/checks.lean.txt`, `docs/design/torus-lattice/checks2.lean.txt` | the `#check`s of §2 |
| `docs/design/torus-lattice/num_bessel.py` | numerics: lattice-Laplacian kernel, rate t^{-2/3} |
| `docs/design/torus-lattice/num_fold.py`, `docs/design/torus-lattice/num_fold2.py` | numerics: search for periodic phases that are fold-or-nondegenerate everywhere |

---

## 0. Summary of the design decisions

1. **Phases and amplitudes are periodic functions on `ℝ × ℝ`** (`Function.Periodic f (2π, 0) ∧ Function.Periodic f
   (0, 2π)`), and the torus integral is a set integral over `Icc (-π) π ×ˢ Icc (-π) π`. Not `AddCircle`: all
   hypotheses of S2–S4 (`dd`, `ddd`, `hessDet`, `IsCritical`, `FoldOrNondeg`, `cubicCoeffs`, `AmpBound`) are written
   with `fderiv`/`iteratedFDeriv` on the normed space `ℝ × ℝ`; Mathlib at the pin has no differential calculus on
   `AddCircle` (no `ChartedSpace`/`IsManifold` instance for `AddCircle` found by grep). An `AddCircle`/
   `UnitAddTorus` front end (the kernel as `UnitAddTorus.mFourierCoeff`) is a later bridge (§1.6).
2. **The reduction is one unfolding identity plus a finite localisation** (T1, T2): a periodic integral equals
   `∫_{ℝ²} χ f` for one fixed smooth compactly supported `χ`, and more generally `Σ_{i ∈ s} ∫_{ℝ²} χ_i f` for a finite
   smooth family subordinate to any open cover. Then the frozen S2.1, S2.2, S3, S4.1′ apply verbatim with
   `m = t` and linear term `p = x/t` (S2.1–S3) or `y = x` (S4.1′).
3. **Uniformity in `x/t ∈ ℝ²`** (not compact): split at `‖x/t‖ = G + 1`, `G` a bound for `∂ᵢθ`. Far velocities: S2.1
   with `c = 1` (it is uniform over *all* `p` with the gradient bound). Near velocities: a compact `K'` for S2.2/S3;
   S4.1′ is uniform over all `y` anyway.
4. **Hypothesis classes.** σ = 1 cannot hold for all `x` (T7: every periodic phase has a degenerate Hessian
   somewhere, PROVEN), so σ = 1 is a *cone* statement (T4). σ = 2/3 holds on all of ℤ² for the 2D lattice Laplacian
   (T6 hypotheses verified by hand, PROVEN; rate sharp numerically, VALIDATED). σ = 5/6 *globally* (T5) is probably
   vacuous for periodic phases (CONJECTURED, numerics: cusps appear), so the primary statements are the cone
   versions T4, T5′, T6′ with hypotheses only at critical points, and the global T6.
5. **1D first** (T0): the 1D lattice kernel `t^{-1/3}` follows from the frozen S1.2/S1.3 alone, on subintervals,
   without cutoffs. Smallest useful deliverable.

---

## 1. Statements (draft Lean)

All drafts live in `namespace OscInt.Statements.Draft` and reuse the frozen definitions `lin`, `oscInt2`, `dd`,
`ddd`, `hessDet`, `IsCritical`, `GradLower`, `FoldOrNondeg`, `AmpBound`, `FamilyCk`, `cubicCoeffs`, `disc`. The text
below is copied from `TorusDraft.lean`, which elaborates (VALIDATED).

### 1.1 Definitions

```lean
open Set MeasureTheory Complex OscInt.Statements
open scoped ContDiff

/-- `f` is `2π`-periodic in each coordinate. -/
def Periodic2 {β : Type} (f : ℝ × ℝ → β) : Prop :=
  Function.Periodic f ((2 * Real.pi, 0) : ℝ × ℝ) ∧ Function.Periodic f ((0, 2 * Real.pi) : ℝ × ℝ)

/-- The fundamental box `[-π, π]²`. -/
def torusBox : Set (ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi

/-- A lattice point as a point of `ℝ²`. -/
def latticePt (x : ℤ × ℤ) : ℝ × ℝ := ((x.1 : ℝ), (x.2 : ℝ))

/-- `K_t(x) = ∫_{[-π,π]²} e^{i(tθ(k) + x·k)} a(k) dk`. -/
noncomputable def latticeKernel (θ : ℝ × ℝ → ℝ) (a : ℝ × ℝ → ℂ) (t : ℝ) (x : ℤ × ℤ) : ℂ :=
  ∫ k in torusBox, Complex.exp (↑(t * θ k + lin (latticePt x) k) * Complex.I) * a k

/-- Periodic amplitude bound `(n, M)`: `a ∈ Cⁿ`, periodic, derivatives of order `≤ n` bounded by `M`. -/
def PerAmpBound (n : ℕ) (a : ℝ × ℝ → ℂ) (M : ℝ) : Prop :=
  ContDiff ℝ n a ∧ Periodic2 a ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j a k‖ ≤ M

/-- At `k` the Hessian vanishes and the cubic part has nonzero discriminant (a D4 point). -/
def IsD4Point (θ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : Prop :=
  (∀ v w, dd θ k v w = 0) ∧ disc (cubicCoeffs (fun κ => θ (k + κ))) ≠ 0
```

Modelling choices (to go in the Lean header, as in `StationaryPhase.lean`):
- **Why `Function.Periodic` on `ℝ × ℝ` and not `AddCircle`.** (i) The hypotheses must be the frozen ones, which are
  stated with `fderiv` on `ℝ × ℝ`; restating them on `AddCircle (2π) × AddCircle (2π)` would need manifold
  derivatives (`mfderiv`) and a new conversion layer for every hypothesis. (ii) The proof unfolds the torus integral
  to `ℝ²` anyway (T1), so the lift is what the proof uses. (iii) Every lattice paper writes the symbol as a
  trigonometric polynomial on `ℝ²`. The `AddCircle` form is a front end (§1.6), not the frozen statement.
- **`Icc` box.** The user-facing form; `Icc` and `Ioc` differ by a null set (the integrand is continuous). The
  integral over any translate of the box is the same for `x ∈ ℤ²` because the integrand is then periodic.
- **`x : ℤ × ℤ`.** For `x ∉ ℤ²` the integrand is not periodic and the box integral is a compactly supported integral
  with a *discontinuous* amplitude `1_box · a`, outside S2–S4; the kernel is only defined on the lattice.
- **Normalisation.** No `(2π)^{-2}`; it only rescales `C`.
- **Amplitude.** `PerAmpBound n a M` is `AmpBound` without the support clause and with periodicity; for a periodic
  `Cⁿ` amplitude such an `M` always exists (periodic continuous functions are bounded; this is a bridge lemma, F1
  analogue). Matrix-valued amplitudes (band projectors of quantum walks) are handled entrywise.
- **Time.** `t : ℝ`, `1 ≤ t`; discrete time `t = n ∈ ℕ` (quantum walks, `U^n`) is the special case.
- **`IsD4Point` translates** `θ` to put `k` at the origin because `cubicCoeffs` is defined at `0`.
- **Constants** come after `θ`, `V`, `N`, `G` and before `a`, `M`, `t`, `x` (as in S2–S4).

### 1.2 (a) The reduction

```lean
/-- **T1** Unfolding: one smooth compactly supported cutoff turns the torus integral of every continuous
periodic function into an integral over `ℝ²`. -/
def TorusUnfoldStatement : Prop :=
  ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    ∀ f : ℝ × ℝ → ℂ, Continuous f → Periodic2 f →
      ∫ k in torusBox, f k = ∫ k, (χ k : ℂ) * f k

/-- **T2** Localisation: for every open cover of `ℝ²` there are finitely many smooth compactly supported
cutoffs, each supported in one member of the cover, splitting every torus integral. -/
def TorusLocalizeStatement : Prop :=
  ∀ (ι : Type) (U : ι → Set (ℝ × ℝ)), (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    ∃ (s : Finset ι) (χ : ι → ℝ × ℝ → ℝ),
      (∀ i ∈ s, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U i) ∧
      ∀ f : ℝ × ℝ → ℂ, Continuous f → Periodic2 f →
        ∫ k in torusBox, f k = ∑ i ∈ s, ∫ k, (χ i k : ℂ) * f k
```

How (a) feeds the frozen statements. For `x ∈ ℤ²`, `f(k) = e^{i(tθ(k) + x·k)} a(k)` is continuous and periodic, so
`K_t(x) = Σ_i ∫ e^{i t(θ(k) + (x/t)·k)} χ_i(k) a(k) dk = Σ_i oscInt2 (fun k => t * (θ k + lin (t⁻¹ • x) k)) (χ_i · a)`,
which is the left side of S2.1/S2.2/S3 with `Ψ = θ`, `m = t`, `p = x/t`, `A = χ_i a`, `K = tsupport χ_i`; and,
after translating `k = k₀ + κ` (`integral_add_right_eq_self`, a unimodular factor `e^{i x·k₀}`), the left side of
S4.1′ with `φ = θ(k₀ + ·)`, `y = x`. `AmpBound 2 K (χ_i a) (C_χ M)` follows from `PerAmpBound 2 a M` by Leibniz
(`norm_iteratedFDeriv_mul_le`), `C_χ = 4 max_{j ≤ 2} sup ‖D^j χ_i‖` (PROVEN: binomial sum ≤ 2^j · max).

PROVEN (paper) for T1 with the explicit cutoff `ψ(s) = S(s + π) − S(s − π)`, `S = Real.smoothTransition`
(0 on `(−∞, 0]`, 1 on `[1, ∞)`), `χ(k) = ψ(k₁) ψ(k₂)`, `supp ψ ⊆ [−π, π + 1]`: for 2π-periodic continuous `g`,
`∫_ℝ ψ g = ∫_{−π}^{1−π} S(s+π) g + ∫_{1−π}^{π} g + ∫_{π}^{π+1} (1 − S(s−π)) g`, and the last term equals
`∫_{−π}^{1−π} (1 − S(s+π)) g` by `s ↦ s − 2π`; the sum is `∫_{−π}^{π} g`. The 2D identity follows by Fubini
(`setIntegral_prod`, `integral_prod`) applied to `χ = ψ ⊗ ψ`. (Equivalently `Σ_{n ∈ ℤ} ψ(s + 2πn) = 1` by
telescoping, but the tsum is not needed.)

### 1.3 (b) Decay theorems

```lean
/-- **T3** Outside the light cone: `|K_t(x)| ≤ C M |x|^{-N}` when `|x| ≥ (G + 1) t`, `G` a bound on `∇θ`. -/
def LatticeLightConeStatement : Prop :=
  ∀ (N : ℕ) (θ : ℝ × ℝ → ℝ) (G : ℝ), ContDiff ℝ (N + 1) θ → Periodic2 θ →
    (∀ k, |fderiv ℝ θ k (1, 0)| ≤ G ∧ |fderiv ℝ θ k (0, 1)| ≤ G) →
    ∃ C : ℝ, ∀ (a : ℝ × ℝ → ℂ) (M t : ℝ) (x : ℤ × ℤ),
      PerAmpBound N a M → 1 ≤ t → (G + 1) * t ≤ ‖latticePt x‖ →
        ‖latticeKernel θ a t x‖ ≤ C * M / ‖latticePt x‖ ^ N

/-- **T4** Nondegenerate cone (σ = 1): `|K_t(x)| ≤ C M t^{-1}` for `x/t` in a compact set `V` of velocities at which
every critical point is nondegenerate. -/
def LatticeConeNondegStatement : Prop :=
  ∀ (θ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ)), ContDiff ℝ 4 θ → Periodic2 θ → IsCompact V →
    (∀ v ∈ V, ∀ k, IsCritical θ v k → hessDet θ k ≠ 0) →
    ∃ C : ℝ, ∀ (a : ℝ × ℝ → ℂ) (M t : ℝ) (x : ℤ × ℤ),
      PerAmpBound 2 a M → 1 ≤ t → t⁻¹ • latticePt x ∈ V →
        ‖latticeKernel θ a t x‖ ≤ C * M / t

/-- **T5′** Folds in a cone (σ = 5/6): fold-or-nondegenerate at every critical point for velocities in `V`. -/
def LatticeConeFoldStatement : Prop :=
  ∀ (θ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ)), ContDiff ℝ 4 θ → Periodic2 θ → IsCompact V →
    (∀ v ∈ V, ∀ k, IsCritical θ v k → FoldOrNondeg θ k) →
    ∃ C : ℝ, ∀ (a : ℝ × ℝ → ℂ) (M t : ℝ) (x : ℤ × ℤ),
      PerAmpBound 2 a M → 1 ≤ t → t⁻¹ • latticePt x ∈ V →
        ‖latticeKernel θ a t x‖ ≤ C * M * t ^ (-(5 : ℝ) / 6)

/-- **T6′** D4 in a cone (σ = 2/3): nondegenerate, fold or D4 at every critical point for velocities in `V`. -/
def LatticeConeD4Statement : Prop :=
  ∀ (θ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ)), ContDiff ℝ 4 θ → Periodic2 θ → IsCompact V →
    (∀ v ∈ V, ∀ k, IsCritical θ v k → FoldOrNondeg θ k ∨ IsD4Point θ k) →
    ∃ C : ℝ, ∀ (a : ℝ × ℝ → ℂ) (M t : ℝ) (x : ℤ × ℤ),
      PerAmpBound 2 a M → 1 ≤ t → t⁻¹ • latticePt x ∈ V →
        ‖latticeKernel θ a t x‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)

/-- **T6** D4, all of ℤ²: if every point is nondegenerate, a fold or a D4 point, `sup_x |K_t(x)| ≤ C M t^{-2/3}`. -/
def LatticeD4Statement : Prop :=
  ∀ θ : ℝ × ℝ → ℝ, ContDiff ℝ 4 θ → Periodic2 θ → (∀ k, FoldOrNondeg θ k ∨ IsD4Point θ k) →
    ∃ C : ℝ, ∀ (a : ℝ × ℝ → ℂ) (M t : ℝ) (x : ℤ × ℤ),
      PerAmpBound 2 a M → 1 ≤ t → ‖latticeKernel θ a t x‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)

/-- **T5** Folds, all of ℤ² (NOT recommended for freezing, see 1.4). -/
def LatticeFoldStatement : Prop :=
  ∀ θ : ℝ × ℝ → ℝ, ContDiff ℝ 4 θ → Periodic2 θ → (∀ k, FoldOrNondeg θ k) →
    ∃ C : ℝ, ∀ (a : ℝ × ℝ → ℂ) (M t : ℝ) (x : ℤ × ℤ),
      PerAmpBound 2 a M → 1 ≤ t → ‖latticeKernel θ a t x‖ ≤ C * M * t ^ (-(5 : ℝ) / 6)

/-- **T7** (obstruction: why T4 is a cone statement) A periodic `C³` phase has a degenerate Hessian somewhere. -/
def TorusHessDegenerateStatement : Prop :=
  ∀ θ : ℝ × ℝ → ℝ, ContDiff ℝ 3 θ → Periodic2 θ → ∃ k, hessDet θ k = 0

/-- **T0** One dimension (S1 route): `|∫_{-π}^{π} e^{i(tθ(k) + xk)} a(k) dk| ≤ C M t^{-1/3}` when `θ''` and
`θ'''` never vanish together. -/
def LatticeOneDimStatement : Prop :=
  ∀ θ : ℝ → ℝ, ContDiff ℝ 3 θ → Function.Periodic θ (2 * Real.pi) →
    (∀ k, iteratedDeriv 2 θ k ≠ 0 ∨ iteratedDeriv 3 θ k ≠ 0) →
    ∃ C : ℝ, ∀ (a : ℝ → ℂ) (M t : ℝ) (x : ℤ),
      ContDiff ℝ 1 a → Function.Periodic a (2 * Real.pi) → (∀ k, ‖a k‖ ≤ M ∧ ‖deriv a k‖ ≤ M) → 1 ≤ t →
        ‖∫ k in (-Real.pi)..Real.pi, Complex.exp (↑(t * θ k + x * k) * Complex.I) * a k‖ ≤
          C * M * t ^ (-(1 : ℝ) / 3)
```

### 1.4 Classification of the hypotheses, and what is (not) satisfiable

`IsCritical θ v k` means `∇θ(k) + v = 0`. Every `k` is critical for `v = −∇θ(k)`, so "for all `v ∈ ℝ²`, every
critical point is X" is the same as "every point of the torus is X". This is why the cone/global split matters.

| Class | Hypothesis | σ | Statement | Satisfiable by a periodic θ? |
|---|---|---|---|---|
| nonstationary | `‖x/t‖ ≥ G + 1` | any N (in `\|x\|^{-N}`) | T3 | always |
| nondegenerate, cone | critical points of `θ + v·` nondegenerate for `v ∈ V` | 1 | T4 | yes: lattice Laplacian, `V = closedBall 0 1` (max norm) (PROVEN: a critical point has `2\|sin kᵢ\| = \|vᵢ\| ≤ 1`, so `cos kᵢ ≠ 0`, Hessian `diag(−2cos k₁, −2cos k₂)` invertible) |
| nondegenerate, global | `hessDet θ ≠ 0` everywhere | 1 | — | **never** (T7, PROVEN below) |
| fold, cone | fold-or-nondeg at critical points, `v ∈ V` | 5/6 | T5′ | yes whenever `V` avoids the velocities of D4/cusp points, e.g. lattice Laplacian with `V` a small ball around `(2, 0)` (PLAUSIBLE; not checked by hand) |
| fold, global | fold-or-nondeg everywhere | 5/6 | T5 | **CONJECTURED never** (numerics below); do not freeze T5 without a sanity example |
| D4, cone / global | fold, nondeg or D4 at critical points / everywhere | 2/3 | T6′ / T6 | yes: lattice Laplacian `2cos k₁ + 2cos k₂` everywhere (PROVEN below) |
| cusp A3 and worse | — | 3/4 (A3), … | none | needs a local A3 statement the library does not have (discrete wave/Klein–Gordon in 2D, §4) |

**T7 is PROVEN** (paper). With `F = ∇θ` (C² since θ ∈ C³), `hessDet θ = det DF = ∂₁(F₁ ∂₂F₂) − ∂₂(F₁ ∂₁F₂)`
(the two `F₁ ∂₁∂₂F₂` terms cancel by symmetry of second derivatives). Both brackets are periodic, so their partial
derivatives integrate to 0 over the box: `∫_box hessDet θ = 0`. If `hessDet θ` never vanished it would have constant
sign on the connected `ℝ²` and a nonzero integral over the box. Alternative (also standard): `∇θ` would be a local
diffeomorphism from the compact torus to ℝ², with open and compact nonempty image. Consequence: a uniform σ = 1 bound
over all `x ∈ ℤ²` is impossible from S2.2, and T4 is necessarily a cone statement.

**Lattice Laplacian satisfies T6's hypothesis: PROVEN** (hand computation; a Lean sanity theorem is part of the
work). `θ = 2cos k₁ + 2cos k₂`, Hessian `diag(−2cos k₁, −2cos k₂)`. (i) both `cos kᵢ ≠ 0`: `hessDet ≠ 0`. (ii)
exactly one, say `cos k₁ = 0`: rank one, kernel `e₁`, `∂³₁₁₁θ = 2 sin k₁ = ±2 ≠ 0`: fold. (iii) `cos k₁ = cos k₂ = 0`:
`D²θ = 0`, cubic part `(sin k₁/3) κ₁³ + (sin k₂/3) κ₂³`, i.e. `a = ±1/3, b = c = 0, d = ±1/3`,
`disc = −27 a² d² = −1/3 < 0`: a hyperbolic umbilic D4⁺ (S4.1′ applies, even S4.1). Draft `Periodic2 latticeLaplacian`
is already proved in `TorusDraft.lean` (VALIDATED).

**Sharpness, VALIDATED (numerics only).** `K_t(x) = (2π)² i^{x₁+x₂} J_{x₁}(2t) J_{x₂}(2t)` (Bessel's integral; the
1D identity was checked by quadrature at three points to 1e-15). `t^{2/3} sup_x |K_t(x)|` = 11.55, 11.45, 11.36,
11.35, 11.34, 11.33, 11.33 for t = 10, 30, 100, 300, 1000, 3000, 10000 (`num_bessel.py`): the exponent 2/3 of T6 is
attained, at `x ≈ (2t, 2t)`, the velocity of the D4 point `(π/2, π/2)`. (`sup_n |J_n(2t)| t^{1/3} → 0.5357 ≈
0.6749 · 2^{−1/3}`, consistent with Landau's constant 0.674885; Landau's bound is quoted from memory, not re-checked.)

**T5 probably vacuous: CONJECTURED.** `num_fold.py` draws 400 random trigonometric polynomials (8 Fourier modes) and
measures `min ‖D²θ‖` over the torus and `min |D³θ[v, v, v]|` (v unit kernel vector) over the parabolic curve
`{hessDet = 0}`; the best candidates on a 160-grid had both ≥ 0.09, but on a 600-grid the second minimum dropped to
0.001–0.011 (cusps). The structured family `cos k₁ + cos k₂ + c cos k₁ cos k₂` (`num_fold2.py`) has no D²θ = 0 point
for `c ∉ {0, ±1}` (PROVEN by a short case analysis) but has cusps (minimum 0 to grid precision) for every
`c ∈ {0.3, 0.5, 0.8, 1.5, 3}`. Heuristic: perturbing a D4 point produces cusps (one for D4⁺, three for D4⁻, a
classical unfolding fact, not re-checked), and no periodic example without cusps or D4 points was found. Whether
every periodic θ on T² has a non-fold degenerate point is OPEN here. Policy consequence: the repository's sanity
rule (every hypothesis set satisfiable by non-degenerate data) cannot currently be met for T5, so only T5′ should be
frozen.

### 1.5 Uniformity in `x/t ∈ ℝ²` (why the far region is free)

Let `G` bound `|∂ᵢθ|` (exists: `∂ᵢθ` continuous and periodic; a 2D boundedness lemma is a gap, §2). If
`‖x/t‖_∞ ≥ G + 1`, then some `|(x/t)ᵢ| ≥ G + 1`, so `|∂ᵢθ(k) + (x/t)ᵢ| ≥ 1` for every `k`, hence
`GradLower θ (x/t) k 1` on every `K`. S2.1 (Λ = a point, `N = 1`, `c = 1`) is uniform over **all** such `p`, giving
`‖oscInt2 …‖ ≤ C M / t ≤ C M t^{-σ}` for each cutoff piece (σ ≤ 1, `t ≥ 1`, `Real.rpow_le_rpow_of_exponent_ge`). For
`‖x/t‖_∞ ≤ G + 1`, `p = x/t` lies in the compact `K' = closedBall 0 (G + 1)` required by S2.2/S3. S4.1′ is uniform
over all `y ∈ ℝ²` and needs no split. In T4/T5′/T6′, `K'` is `V` itself and the far region is not needed; T6
(global) is T6′ with `V = closedBall 0 (G + 1)` plus the far region.

T3 (`|x|^{-N}` decay, not only `t^{-N}`) needs S2.1 with a genuine compact family: write
`tθ(k) + x·k = ‖x‖ (s θ(k) + ω·k)`, `s = t/‖x‖ ∈ [0, 1/(G+1)]`, `ω = x/‖x‖ ∈ sphere 0 1` (compact,
`isCompact_sphere`), `Λ = Icc 0 (1/(G+1)) × sphere 0 1`, `Ψ_{(s,ω)}(k) = sθ(k) + ω·k`, `p = 0`, `m = ‖x‖ ≥ 1`,
`|∇Ψ| ≥ 1 − sG ≥ 1/(G+1)` in the coordinate where `|ωᵢ| = 1`. PLAUSIBLE (only the max-norm bookkeeping and the
`FamilyCk` joint continuity need care).

### 1.6 Front end on Mathlib's torus (later batch, not for the first freeze)

```lean
noncomputable def torusKernel (Θ : UnitAddTorus (Fin 2) → ℝ) (α : UnitAddTorus (Fin 2) → ℂ) (t : ℝ)
    (n : Fin 2 → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun z => Complex.exp (↑(t * Θ z) * Complex.I) * α z) n
```
(elaborates, VALIDATED). Bridge: if `θ(k) = Θ(k/2π)` (lift through `fun i => ↑(k i / 2π)`), then
`torusKernel Θ α t n = (2π)^{-2} latticeKernel θ a t (−n)`, via `UnitAddTorus.integral_preimage` and a linear change
of variables. Period 1 and `Fin 2 → ℝ` (sup norm, `EuclideanSpace` not involved) differ from the core's `ℝ × ℝ`; the
bridge is about 150–250 lines (PLAUSIBLE).

---

## 2. Mathlib names: checked and missing

Checked at the pin with `#check` in `checks.lean`/`checks2.lean` (`lake env lean`, VALIDATED; signatures abbreviated).

| Name | Signature (essentials) | Use |
|---|---|---|
| `Function.Periodic` | `[Add α] (f : α → β) (c : α) : Prop` | `Periodic2` (works on `ℝ × ℝ` with `c = (2π, 0)`) |
| `AddCircle`, `AddCircle.intervalIntegral_preimage` | `(t) (f : AddCircle T → E) : ∫ a in t..t+T, f ↑a = ∫ b, f b` | front end |
| `AddCircle.integral_preimage` | same with `Set.Ioc t (t + T)` | front end |
| `UnitAddTorus` | `abbrev UnitAddTorus d := d → UnitAddCircle` | front end |
| `UnitAddTorus.integral_preimage` | `∫ x, f x = ∫ x in {x \| ∀ i, x i ∈ Ioc (a i) (a i + 1)}, f (fun i => ↑(x i))` | front end bridge |
| `UnitAddTorus.mFourierCoeff`, `UnitAddTorus.mFourier` | `(f : UnitAddTorus d → E) (n : d → ℤ) : E` | front end |
| `fourierCoeffOn` | `a < b → (ℝ → E) → ℤ → E` | 1D front end for T0 |
| `Real.smoothTransition`, `.zero_of_nonpos`, `.one_of_one_le`, `.contDiff` | `x ≤ 0 → … = 0`; `1 ≤ x → … = 1`; `ContDiff ℝ ↑n` for `n : ℕ∞` | the cutoff ψ of T1 |
| `exists_contDiff_tsupport_subset` | `s ∈ 𝓝 x → ∃ f, tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ f x = 1` | local bumps in T2 |
| `SmoothPartitionOfUnity.exists_isSubordinate` | manifold version: `IsClosed s → (U open) → s ⊆ ⋃ U → ∃ f, f.IsSubordinate U` | T2 (on `ℝ × ℝ` with `𝓘(ℝ, ℝ × ℝ)`) |
| `PartitionOfUnity.exists_isSubordinate` | continuous version | fallback |
| `IsCompact.elim_finite_subcover` | `IsCompact s → (U open) → s ⊆ ⋃ U → ∃ t : Finset, s ⊆ ⋃ i ∈ t, U i` | T2 |
| `MeasureTheory.integral_prod`, `MeasureTheory.setIntegral_prod` | Fubini on `μ.prod ν` (integrability hypothesis) | T1 2D from 1D |
| `MeasureTheory.integral_add_right_eq_self` | `∫ x, f (x + g) ∂μ = ∫ x, f x ∂μ` for right-invariant μ | translation to `k₀` for S4.1′ |
| `MeasureTheory.integral_indicator` | `MeasurableSet s → ∫ s.indicator f = ∫ x in s, f x` | box integral |
| `MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum` | `IsAddFundamentalDomain G s μ → Integrable f μ → ∫ f = ∑' g, ∫ x in g +ᵥ s, f x` | alternative route to T1 |
| `isAddFundamentalDomain_Ioc` | `0 < T → IsAddFundamentalDomain (zmultiples T) (Ioc t (t+T)) μ` | alternative route to T1 (1D) |
| `ZSpan.isAddFundamentalDomain` | fundamental domain of `span ℤ (range b)` for a basis | alternative 2D route (not recommended) |
| `MeasureTheory.Measure.prod.instIsAddHaarMeasure` | product of Haar measures is Haar | invariance on `ℝ × ℝ` |
| `Function.Periodic.intervalIntegral_add_eq` | `∫ t..t+T = ∫ s..s+T` | T0, T1 |
| `Function.Periodic.exists_mem_Ico₀` | `0 < c → ∃ y ∈ Ico 0 c, f x = f y` | 1D reduction to a period |
| `Function.Periodic.isBounded_of_continuous` | **only `f : ℝ → α`** | 1D boundedness (T0) |
| `toIcoMod_add_toIcoDiv_zsmul` | `toIcoMod hp a b + toIcoDiv hp a b • p = b` | 2D reduction to the box |
| `fderiv_comp_add_right` | `fderiv (fun x => f (x + a)) x = fderiv f (x + a)` | periodicity of `∇θ`, `dd`, `ddd` |
| `iteratedFDeriv_comp_add_right` | `iteratedFDeriv n (fun z => f (z + a)) x = iteratedFDeriv n f (x + a)` | periodicity of `D^j a` |
| `norm_iteratedFDeriv_mul_le` | Leibniz bound `‖D^n (f g)‖ ≤ Σ C(n,i) ‖D^i f‖ ‖D^{n−i} g‖` (normed algebra `A`) | `AmpBound` for `χ a` (ℂ is a normed ℝ-algebra) |
| `ContDiff.continuous_iteratedFDeriv` | `↑m ≤ n → ContDiff 𝕜 n f → Continuous (iteratedFDeriv 𝕜 m f)` | bounds, `FamilyCk` |
| `Continuous.bddAbove_range_of_hasCompactSupport` | bounded range | cutoff derivative bounds |
| `IsCompact.exists_bound_of_continuousOn`, `IsCompact.exists_isMinOn` | | `G`, gradient lower bounds on compacts |
| `isCompact_sphere` | `[ProperSpace α] → IsCompact (sphere x r)` | Λ in T3 |
| `HasStrictFDerivAt.map_nhds_eq_of_equiv` | `map f (𝓝 a) = 𝓝 (f a)` | T7 (open-mapping route) |
| `Real.rpow_le_rpow_of_exponent_ge` | `0 < x → x ≤ 1 → z ≤ y → x ^ y ≤ x ^ z` | `t^{-1} ≤ t^{-5/6} ≤ t^{-2/3}` (applied to `t⁻¹`) |
| `Real.cos_add_two_pi` | | sanity: lattice Laplacian periodic (used, VALIDATED) |
| `ContDiffBump` | | alternative cutoffs |
| `Complex.besselJ`, `Complex.besselJ_int_neg` | `ℂ → ℂ → ℂ` (hypergeometric definition) | only for an optional sanity link to Bessel |

Tried and **not present** at the pin (unknown identifier): `HasStrictFDerivAt.map_nhds_eq` (the name is
`…_of_equiv`), `Function.Periodic.integral_add_eq`, `Metric.isCompact_sphere` (it is root `isCompact_sphere`),
`ContDiff.periodic_iteratedFDeriv`, `Function.Periodic.bddAbove_range`. Grep found no Mathlib result about: derivatives
of periodic functions being periodic (follows in 2 lines from `fderiv_comp_add_right`), boundedness of continuous
periodic functions on `ℝ²` (1D only), the unfolding identity `∫_box f = ∫_{ℝ²} χ f` with a periodic partition of
unity, Bessel's integral representation of `J_n` (listed as TODO in `Mathlib/Analysis/SpecialFunctions/Bessel.lean`),
uniform bounds `|J_n(x)| ≤ C x^{-1/3}`, any oscillatory integral estimate (`Mathlib/Analysis/Oscillation.lean` is about
the oscillation of a function, unrelated), or differential calculus on `AddCircle` (no `ChartedSpace`/`IsManifold`
instance for `AddCircle` found by grep).

Gaps to fill in the library (all small, PLAUSIBLE sizes): G1 periodic derivatives (≈ 30 lines); G2 continuous
`Periodic2` functions are bounded and attain extrema (≈ 60, via `toIcoMod` reduction to the compact box); G3 the 1D
unfolding identity with `smoothTransition` (≈ 120); G4 2D unfolding by Fubini (≈ 100); G5 finite smooth partition on a
compact set subordinate to an open cover (≈ 150; Mathlib's `SmoothPartitionOfUnity` is indexed by the cover and
locally finite, the finite reindexing is the work); G6 Leibniz to `AmpBound` (≈ 60); G7 openness of
`FoldOrNondeg` (≈ 150–250; needs C1/C2 of `docs/statements.md` to pass from nested `fderiv` to continuous
`iteratedFDeriv`, and continuity of the kernel line of a rank-one symmetric 2×2 matrix).

---

## 3. Size estimate and proof route

### 3.1 Route per statement (frozen statements used as black boxes)

- **T0 (1D)** — black boxes **S1.2** (`OscInt.vanDerCorput_two`) and **S1.3** (`OscInt.vanDerCorput_three`). By
  compactness of `[−π, π]` and continuity, cover it by finitely many closed intervals on each of which
  `|θ''| ≥ c` or `|θ'''| ≥ c` (`c > 0` from the hypothesis). On each interval apply S1.2 with `φ = tθ`,
  `|φ''| ≥ tc`, or S1.3 with `|φ'''| ≥ tc`; the linear term `xk` is S1's `p`. Amplitude term
  `A(ψ; a, b) ≤ M (1 + 2π)`. Bound `Σ (8 (tc)^{-1/2} + 18 (tc)^{-1/3}) M (1 + 2π) ≤ C M t^{-1/3}`. No cutoffs, no
  unfolding. Constants are explicit in principle. PLAUSIBLE.
- **T1, T2** — Mathlib only (G3–G5).
- **T3** — **S2.1** with the compact family of §1.5 (`OscInt.nonStationary`), after T1.
- **T4** — T1 + **S2.2** (`OscInt.stationaryPhase`) with `Ψ = θ`, `K = tsupport χ`, `K' = V`, `m = t`, `p = x/t`;
  hypothesis on `K` from the hypothesis on all `k`. G6 for the amplitude.
- **T5′** — T2 with the cover: for `k` with `−∇θ(k) ∈ V` an open ball on whose closure `FoldOrNondeg` holds (G7); for
  other `k` an open ball on whose closure `dist(−∇θ, V) ≥ c_k > 0` (continuity + compact `V`). Pieces of the first kind:
  **S3** (`OscInt.fold`, Λ = `Unit`, `FamilyCk` from `sanity_familyCk_const`, `K'` = `V`); second kind: **S2.1** with
  `c = c_k`, `N = 1`. Finitely many pieces, sum of constants.
- **T6′** — as T5′ plus, for D4 points `k₀`, the open max-norm ball of the radius δ given by **S4.1′**
  (`OscInt.d4BoundNe`) for `φ = θ(k₀ + ·)`; translate the piece by `k₀` (`integral_add_right_eq_self`), apply S4.1′
  with `y = x` and amplitude `κ ↦ χ_i(k₀ + κ) a(k₀ + κ)`. No discreteness of the D4 set is needed: the cover is
  indexed by all points and T2 extracts a finite subfamily.
- **T6** — T6′ with `V = closedBall 0 (G + 1)` (hypothesis at every `k` implies it at critical points) plus the far
  region by S2.1 (§1.5). Note the global hypothesis needs no openness lemma if one indexes the cover by D4 points
  and uses the closed complement, but G7 is needed for T5′/T6′ anyway.
- **T7** — divergence identity + periodic integral of a derivative vanishes (1D FTC per row, Fubini) + intermediate
  value on the connected `ℝ²`; or the open-mapping route via `HasStrictFDerivAt.map_nhds_eq_of_equiv`. Mathlib only.
- **Sanity** — lattice Laplacian: `Periodic2` (done), the trichotomy of §1.4 (`dd`, `ddd` of `cos` through C1/C2 or
  by direct `HasFDerivAt` computations as in `StationaryPhase.lean`), `disc = −1/3`; T4's hypothesis with
  `V = closedBall 0 1`; a `PerAmpBound` witness (`a = 1`).

### 3.2 Size (PLAUSIBLE; calibrated on the repository's S2/S3 assembly files, not measured)

| Part | Content | Lines |
|---|---|---|
| P1 Statements | defs, T0–T7, sanity theorems, header | 250–400 |
| P2 Periodic infrastructure | G1, G2, G6, `Periodic2` lemmas, box ↔ translate | 200–300 |
| P3 Unfolding and localisation | G3, G4, G5 → T1, T2 | 350–550 |
| P4 1D | T0 from S1 | 200–350 |
| P5 Far region and cone σ = 1 | T3 (compact family), T4 | 300–450 |
| P6 Openness + folds | G7, T5′ | 300–450 |
| P7 D4 | T6′, T6 | 250–400 |
| P8 Obstruction and front end | T7; `UnitAddTorus` bridge (optional) | 200–450 |
| **Total** | 8 parts | **≈ 2,000–3,300** |

Order: P1 (stamp, blind review) → P2, P3, P4 in parallel → P5 → P6 → P7 → P8. T0 + T1 + T6 for the lattice
Laplacian is the shortest path to the headline application ("2D lattice Schrödinger: `sup_x |K_t(x)| ≲ t^{-2/3}`").

---

## 4. Prior-art sweep (2026-11-07)

Tools used: local grep of Mathlib at the pin; WebSearch (general web) and WebFetch (arXiv abstract and HTML pages);
`gh search code` (GitHub code search, language Lean) and raw downloads from `raw.githubusercontent.com` (files read
are marked R). The GitHub API for repository listing was not available from this session, and the Lean Zulip archive
was not searchable (web search returned no Zulip hits); Isabelle AFP, Rocq and HOL were not re-searched (the
2026-11-05 gate in `docs/prior_art.md` found nothing there for oscillatory integrals). **No near-duplicate found in
the sweep listed** (PLAUSIBLE-not-novel: the sweep can miss Zulip threads, private repositories and unindexed code).

### 4.1 Formalisations

| Item | URL | What it has | Relation | Read |
|---|---|---|---|---|
| Mathlib at the pin | local | no oscillatory integral estimates; `Complex.besselJ` by the hypergeometric series, Bessel's integral listed as TODO; `UnitAddTorus.mFourierCoeff`; Riemann–Lebesgue (`tendsto_integral_exp_inner_smul_cocompact`) | infrastructure only | R (grep) |
| bjbraams/lean-DLMF `DLMF/Bessel/BesselIntegral.lean` (HEAD `06ad2e43`) | https://github.com/bjbraams/lean-DLMF | Jacobi–Anger expansion, `besselJ_int_eq_integral_exp`: `J_n(z) = (2π)^{-1} ∫₀^{2π} e^{i(z sin θ − nθ)} dθ` — i.e. the 1D lattice kernel of `θ = sin` is a Bessel function; `DLMF/Bessel/LargeOrder.lean`: large-order limits for fixed argument; no `sorry` in the files read | PARTIAL (the exact kernel identity for the lattice Laplacian; no uniform `\|J_n(x)\| ≲ x^{-1/3}` bound found) | R |
| TauCetiProject/TauCeti `TauCeti/Analysis/PDE/Schrodinger/Dispersive.lean` | https://github.com/TauCetiProject/TauCeti | continuum Schrödinger on a finite-dimensional inner product space: explicit kernel and `‖S(t)f‖_∞ ≤ (4π\|t\|)^{-n/2} ‖f‖₁`, via complex Gaussians | ADJACENT (continuum, explicit kernel, no oscillatory-integral estimate) | R |
| TomasOrtega/Sidon `Sidon/NumberTheory/RiemannGaussian/FiniteKuzminLandau.lean`, `DiscreteSecondDerivativeTest.lean` | https://github.com/TomasOrtega/Sidon | Kusmin–Landau first-derivative test for exponential sums `‖Σ e(φ(n))‖ ≤ 2π/η`; a discrete second-derivative test | PARTIAL for "van der Corput for exponential sums" (ROADMAP §5); unrelated to torus integrals | R |
| teorth/expdb `Expdb/ExponentialSums/FixedExponentialSum.lean` | https://github.com/teorth/expdb | definitions and trivial bounds for exponential sums | ADJACENT | R |
| roos-j/lean-oscillatory, Mathlib PR #39406; roos-j/lean-variationalsw, lean-spherical, lean-dfr; bjbraams/lean-DLMF stationary phase; fpvandoorn/carleson | see `docs/prior_art.md` | 1D van der Corput; ℝⁿ non-stationary phase; 1D stationary phase | as in the existing gate (S1 ANTICIPATED, S2 PARTIAL); none treats periodic/lattice kernels | from gate |
| rwst/lean-code, plby/lean-proofs, LeanPool QuadraticCarleson (code-search hits for "van der Corput") | GitHub | van der Corput difference inequality / equidistribution; Carleson-type decay | UNRELATED to lattice kernels | search hit only |
| emberian/obend `Analysis/QuantumWalk.lean`; QudeLeap/Lean-QuantumAlg `Analysis/Walk/*` | GitHub | continuous-time quantum walks on finite graphs (perfect state transfer, spectral projectors); search-algorithm walk operators | UNRELATED (finite graphs, no dispersive decay) | R (headers) |
| Code search "lattice Green" (Lean) | GitHub | no hits | not found | — |
| arXiv / web searches "Lean formalization" × {dispersive, lattice Green function, quantum walk, exponential sum, van der Corput} | — | no formalisation found | not found | — |

### 4.2 Classical mathematical sources

| Source | Claim used here | Checked against |
|---|---|---|
| A. Stefanov, P. G. Kevrekidis, *Asymptotic behaviour of small solutions for the discrete nonlinear Schrödinger and Klein–Gordon equations*, Nonlinearity 18(4) (2005) 1841–1857, doi:10.1088/0951-7715/18/4/022, arXiv:nlin/0409009 | `‖U(t)f‖_{ℓ^∞} ≤ C (1+\|t\|)^{-d/3} ‖f‖_{ℓ¹}` for the discrete Schrödinger and Klein–Gordon propagators on ℤ^d; d = 1: t^{-1/3}, d = 2: t^{-2/3} (the latter by the product structure) | arXiv abstract page (read); journal data from the reference list of Bi–Cheng–Hua (read). Note: the user's phrasing "t^{-1/3}/t^{-2/3} in 1D/2D" agrees with d/3; for **Klein–Gordon** the d/3 rate is **not** sharp (Cuenin–Ikromov) |
| J.-C. Cuenin, I. A. Ikromov, *Sharp time decay estimates for the discrete Klein–Gordon equation*, Nonlinearity 34 (2021) 7938–7962, doi:10.1088/1361-6544/ac2b86, arXiv:2011.12076 | discrete KG on ℤ^d: `\|t\|^{-3/4}` (d = 2), `\|t\|^{-7/6}` (d = 3), `\|t\|^{-3/2} log\|t\|` (d = 4), faster than conjectured by Kevrekidis–Stefanov | arXiv abstract (read) |
| P. Schultz, *The wave equation on the lattice in two and three dimensions*, Comm. Pure Appl. Math. 51(6) (1998) 663–695 | 2D lattice wave equation decays like `\|t\|^{-3/4}`, 3D like `\|t\|^{-7/6}` | **not re-checked against the original**; bibliographic data and the rates read in Bi–Cheng–Hua arXiv:2312.04130v3 (HTML, read). A web-search summary attributed `\|t\|^{-2/3}` (d = 2) to Schultz in arXiv:2406.00949; that page was not read, discrepancy unresolved |
| C. Bi, J. Cheng, B. Hua, *The wave equation on lattices and oscillatory integrals*, arXiv:2312.04130 | sharp dispersive estimates for the wave equation on ℤ⁴ (`\|t\|^{-3/2} log\|t\|`), Newton-polyhedron interpretation for d = 2, 3, 4; uses singularity theory (A_k, D4⁻) | arXiv abstract and HTML (read, through the fetch tool's summary) |
| I. Borovyk, M. Goldberg, *The Klein–Gordon equation on ℤ² and the quantum harmonic lattice*, J. Math. Pures Appl. (9) 107(6) (2017) 667–696 | 2D discrete KG decay | reference list of Bi–Cheng–Hua only; content **not re-checked** |
| M. Maeda, H. Sasaki, E. Segawa, A. Suzuki, K. Suzuki, *Dispersive estimates for quantum walks on 1D lattice*, J. Math. Soc. Japan 74(1) (2022) 217–246(?), arXiv:1808.05714 | `‖U^t P_c u₀‖_{ℓ^∞} ≲ (1+\|t\|)^{-1/3} ‖u₀‖_{ℓ¹}` for 1D quantum walks with position-dependent coin | arXiv abstract (read); journal volume/issue from the J-STAGE search result; page range **not re-checked** |
| A. N. Varchenko, *Newton polyhedra and estimates of oscillatory integrals*, Funct. Anal. Appl. 10 (1976) | oscillation indices (1 for A1, 5/6 for A2, 3/4 for A3, 2/3 for D4 in two variables) | reference list of Bi–Cheng–Hua (bibliographic only); the index values are standard (Arnold–Gusein-Zade–Varchenko), **not re-checked** here |
| L. J. Landau, *Bessel functions: monotonicity and bounds*, J. London Math. Soc. (2000) | `sup_ν \|J_ν(x)\| ≤ b x^{-1/3}`, `b ≈ 0.6749` | **not re-checked** (quoted from memory; the numerics above are consistent) |

Consequences for scope (PLAUSIBLE): the library's singularity menu (A1, A2, D4) covers the 2D lattice
**Schrödinger** kernel (T6, sharp) and quantum-walk bands whose dispersion relations have only A1/A2/D4 points; it
does **not** cover the 2D discrete **wave/Klein–Gordon** kernels, whose sharp `t^{-3/4}` comes from A3 (cusp) points
(Bi–Cheng–Hua's 2D normal forms include `ξ₁² + ξ₁ξ₂²`, an A3 form) — that needs a new local cusp statement
(uniform `t^{-3/4}`), which would be a natural S5. Genuinely discrete sums (finite periodic lattices, exponential sums
`Σ_{n} e(f(n))`) are a separate design (Poisson summation / B-process), with Kusmin–Landau already formalised in
TomasOrtega/Sidon.

---

## 5. Claims and labels at a glance

| Claim | Label |
|---|---|
| All draft statements elaborate against `OscInt.Statements.D4Limit`; `Periodic2 latticeLaplacian` proved | VALIDATED |
| Every Mathlib name in §2's table exists with the shown signature | VALIDATED |
| T1 unfolding identity with `ψ = S(·+π) − S(·−π)` | PROVEN (paper) |
| T7: a periodic C³ phase has `hessDet = 0` somewhere | PROVEN (paper) |
| Lattice Laplacian: every point nondegenerate / fold / D4⁺ (`disc = −1/3`) | PROVEN (hand computation) |
| Lattice Laplacian with `V = closedBall 0 1`: T4 hypothesis | PROVEN (hand computation) |
| `sup_x \|K_t(x)\|` for the lattice Laplacian decays exactly like `t^{-2/3}` | VALIDATED (numerics; classical via Bessel) |
| Routes for T0, T3, T4, T5′, T6′, T6 from S1/S2.1/S2.2/S3/S4.1′ | PLAUSIBLE |
| Openness of `FoldOrNondeg` (G7) | PLAUSIBLE |
| T5 (global folds) is vacuous for periodic phases | CONJECTURED (numerics) / OPEN |
| Size 2,000–3,300 lines in 8 parts | PLAUSIBLE |
| No formalisation of lattice/torus oscillatory kernels exists | not claimed; "no near-duplicate found in the sweep listed" |
