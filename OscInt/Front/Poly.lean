import OscInt.Statements.Convert
import OscInt.Front.ConvertDeriv

/-!
# Hypothesis helpers for explicit phases (P2)

Lemmas (proved, not frozen statements: they only *produce* the hypotheses of the front ends, whose types are the
frozen statements) that turn an explicit polynomial phase into the derivative data the front ends ask for:

* `iteratedFDeriv_diag_of_poly`: `Dⁿf(k)[v, …, v] = n! cₙ` when `t ↦ f(k + t v) = ∑ cᵢ tⁱ` (prove the expansion by
  `simp; ring`). This gives the cubic identity of FE-S4.1′ and the diagonal second derivatives.
* `iteratedFDeriv_two_polar`: `D²f(k)[u, v] = (D²f(k)[u+v, u+v] − D²f(k)[u, u] − D²f(k)[v, v]) / 2` (symmetry).
* `iteratedFDeriv_two_eq_zero_of_diag`: `D²f(k) = 0` from `D²f(k)[v, v] = 0` for all `v` (FE-S4.1′'s `D²φ(0) = 0`).
* `hessianMatrix_eq_of_diag`: the Hessian matrix from the three diagonal values at `e₀`, `e₁`, `e₀ + e₁`.
* `foldCondSpan_of_rankOne`: the span form of the fold condition from an elementary test (`H ≠ 0`, `det H = 0`, and
  `T` nonzero on every nonzero kernel vector) — no kernel or rank computation by hand.
-/

namespace OscInt.API.Poly

open Polynomial OscInt.Statements

/-- D^n f(k)[v,…,v] is the n-th derivative of t ↦ f(k + t v) at 0. -/
theorem iteratedFDeriv_diag_eq {n : ℕ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ n f) (k v : ℝ × ℝ) :
    iteratedFDeriv ℝ n f k (fun _ => v) = iteratedDeriv n (fun t : ℝ => f (k + t • v)) 0 := by
  let g : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have h1 : (fun t : ℝ => f (k + t • v)) = (fun x => f (k + x)) ∘ g := by
    funext t; simp [g]
  have hc : ContDiff ℝ n (fun x => f (k + x)) := hf.comp (contDiff_const.add contDiff_id)
  rw [h1, iteratedDeriv_eq_iteratedFDeriv, ContinuousLinearMap.iteratedFDeriv_comp_right g hc 0 le_rfl,
    iteratedFDeriv_comp_add_left]
  simp [g]

theorem iteratedDeriv_polyEval (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n (fun t : ℝ => p.eval t) = fun t => (derivative^[n] p).eval t := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', show deriv (fun t : ℝ => p.eval t) = fun t => (derivative p).eval t from
      funext fun t => Polynomial.deriv p, ih, Function.iterate_succ_apply]

theorem iteratedDeriv_polyEval_zero (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n (fun t : ℝ => p.eval t) 0 = n.factorial * p.coeff n := by
  rw [iteratedDeriv_polyEval]
  show eval 0 _ = _
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]

/-- If `t ↦ g t` is the polynomial `∑ i < N, c i tⁱ`, its `n`-th derivative at `0` is `n! c n`. -/
theorem iteratedDeriv_zero_of_poly {N : ℕ} (c : Fin N → ℝ) (g : ℝ → ℝ)
    (hg : ∀ t, g t = ∑ i : Fin N, c i * t ^ (i : ℕ)) (n : Fin N) :
    iteratedDeriv n g 0 = (n : ℕ).factorial * c n := by
  have : g = fun t => (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : ℝ[X]).eval t := by
    funext t; rw [hg]; simp [eval_finsetSum]
  rw [this, iteratedDeriv_polyEval_zero]
  congr 1
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n (fun b _ hb => ite_eq_right (fun h => hb (Fin.ext h.symm))) (by simp)]
  simp

/-- `Dⁿf(k)[v, …, v] = n! cₙ` from an expansion of `t ↦ f (k + t v)` as a polynomial `∑ i < N, cᵢ tⁱ`. -/
theorem iteratedFDeriv_diag_of_poly {N : ℕ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (N : ℕ) f) (k v : ℝ × ℝ)
    (c : Fin N → ℝ) (hc : ∀ t : ℝ, f (k + t • v) = ∑ i : Fin N, c i * t ^ (i : ℕ)) (n : ℕ) (hn : n < N) :
    iteratedFDeriv ℝ n f k (fun _ => v) = n.factorial * c ⟨n, hn⟩ := by
  rw [iteratedFDeriv_diag_eq (hf.of_le (by exact_mod_cast hn.le))]
  exact iteratedDeriv_zero_of_poly c _ hc ⟨n, hn⟩

/-- Polarisation of the second derivative (symmetric for `C²` functions). -/
theorem iteratedFDeriv_two_polar {f : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f k) (u v : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 f k ![u, v] =
      (iteratedFDeriv ℝ 2 f k ![u + v, u + v] - iteratedFDeriv ℝ 2 f k ![u, u] -
        iteratedFDeriv ℝ 2 f k ![v, v]) / 2 := by
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_add,
    add_apply]
  have := OscInt.API.DerivAux.symm2 hf v u
  linarith

theorem iteratedFDeriv_two_eq_zero_of_diag {f : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f k)
    (h : ∀ v, iteratedFDeriv ℝ 2 f k ![v, v] = 0) : iteratedFDeriv ℝ 2 f k = 0 := by
  ext m
  have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
  rw [hm, iteratedFDeriv_two_polar hf, h, h, h]
  simp

/-- The Hessian matrix from the diagonal values at `e₀`, `e₁` and `e₀ + e₁`. -/
theorem hessianMatrix_eq_of_diag {f : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f k) {p q s : ℝ}
    (h0 : iteratedFDeriv ℝ 2 f k ![(1, 0), (1, 0)] = p) (h1 : iteratedFDeriv ℝ 2 f k ![(0, 1), (0, 1)] = q)
    (h01 : iteratedFDeriv ℝ 2 f k ![(1, 1), (1, 1)] = s) :
    hessianMatrix f k = !![p, (s - p - q) / 2; (s - p - q) / 2, q] := by
  have hp : iteratedFDeriv ℝ 2 f k ![(1, 0), (0, 1)] = (s - p - q) / 2 := by
    rw [iteratedFDeriv_two_polar hf, h0, h1, show ((1, 0) + (0, 1) : ℝ × ℝ) = (1, 1) by simp, h01]
  have hp' : iteratedFDeriv ℝ 2 f k ![(0, 1), (1, 0)] = (s - p - q) / 2 := by
    rw [iteratedFDeriv_two_polar hf, h0, h1, show ((0, 1) + (1, 0) : ℝ × ℝ) = (1, 1) by simp, h01]; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessianMatrix, coordVec, h0, h1, hp, hp']

/-- The span form of the fold condition from an elementary rank-one test. -/
theorem foldCondSpan_of_rankOne {H : Matrix (Fin 2) (Fin 2) ℝ} {T : (Fin 2 → ℝ) → ℝ} (hH : H ≠ 0)
    (hdet : H.det = 0) (hT : ∀ e, e ≠ 0 → H.mulVec e = 0 → T e ≠ 0) : FoldCondSpan H T := by
  right
  -- a nonzero kernel vector exists (det = 0), and the kernel is a line (H ≠ 0)
  have hker : ∃ e : Fin 2 → ℝ, e ≠ 0 ∧ H.mulVec e = 0 := by
    obtain ⟨e, he, hHe⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact ⟨e, he, hHe⟩
  obtain ⟨e, he, hHe⟩ := hker
  refine ⟨e, he, ?_, hT e he hHe⟩
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    rw [Submodule.mem_span_singleton]
    by_contra hne
    apply hH
    -- `e` and `v` independent kernel vectors force `H = 0`
    have hind : e 0 * v 1 - e 1 * v 0 ≠ 0 := by
      intro h0
      apply hne
      by_cases h0e : e 0 = 0
      · have h1e : e 1 ≠ 0 := fun h1 => he (by funext i; fin_cases i <;> simp [h0e, h1])
        refine ⟨v 1 / e 1, ?_⟩
        funext i; fin_cases i <;> simp <;> field_simp
        · have : e 1 * v 0 = 0 := by rw [h0e, zero_mul] at h0; linarith
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h h1e
          · rw [h0e, h]; ring
      · refine ⟨v 0 / e 0, ?_⟩
        funext i; fin_cases i <;> simp <;> field_simp
        linarith
    have r0 := congrFun hHe 0; have r1 := congrFun hHe 1
    have s0 := congrFun hv 0; have s1 := congrFun hv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at r0 r1 s0 s1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · have : H 0 0 * (e 0 * v 1 - e 1 * v 0) = 0 := by linear_combination v 1 * r0 - e 1 * s0
      exact (mul_eq_zero.mp this).resolve_right hind
    · have : H 0 1 * (e 0 * v 1 - e 1 * v 0) = 0 := by linear_combination -(v 0) * r0 + e 0 * s0
      exact (mul_eq_zero.mp this).resolve_right hind
    · have : H 1 0 * (e 0 * v 1 - e 1 * v 0) = 0 := by linear_combination v 1 * r1 - e 1 * s1
      exact (mul_eq_zero.mp this).resolve_right hind
    · have : H 1 1 * (e 0 * v 1 - e 1 * v 0) = 0 := by linear_combination -(v 0) * r1 + e 0 * s1
      exact (mul_eq_zero.mp this).resolve_right hind
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply]
    exact hHe

end OscInt.API.Poly
