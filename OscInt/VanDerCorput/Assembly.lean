import Blueprint.VanDerCorput

/-!
# S1 assembly against the blueprint interfaces

`VdC1Statement`, `VdC2Statement`, `VdC3Statement` from the blueprint propositions: the plain bounds hold on every
subinterval `[a, y]` (hypotheses restrict), the linear term `p x` only shifts `φ'` (hypotheses on higher derivatives
are unchanged), and the amplitude transfer turns the uniform subinterval bound into the amplitude form.
-/

namespace OscInt.VanDerCorput

open Set OscInt.Statements OscInt.Blueprint

theorem HasDerivOn.mono {f f' : ℝ → ℝ} {a b c d : ℝ} (h : HasDerivOn f f' a b) (hac : a ≤ c) (hdb : d ≤ b) :
    HasDerivOn f f' c d :=
  ⟨h.1.mono (Icc_subset_Icc hac hdb), fun x hx => h.2 x (Ioo_subset_Ioo hac hdb hx)⟩

theorem HasDerivOn.add_linear {f f' : ℝ → ℝ} {a b : ℝ} (h : HasDerivOn f f' a b) (p : ℝ) :
    HasDerivOn (fun x => f x + p * x) (fun x => f' x + p) a b := by
  refine ⟨h.1.add (continuousOn_const.mul continuousOn_id), fun x hx => ?_⟩
  simpa using (h.2 x hx).fun_add ((hasDerivAt_id' x).const_mul p)

theorem HasDerivOn.add_const {f f' : ℝ → ℝ} {a b : ℝ} (h : HasDerivOn f f' a b) (p : ℝ) :
    HasDerivOn (fun x => f x + p) f' a b :=
  ⟨h.1.add continuousOn_const, fun x hx => (h.2 x hx).add_const p⟩

theorem vdc1_of (h1 : VdC1PlainFacts) (hA : AmplitudeTransferFacts) : VdC1Statement := by
  intro φ φ' φ'' ψ ψ' a b ν hab hν hφ hφ' hmono hlow hψ
  refine hA φ ψ ψ' a b (3 / ν) hab (by positivity) hφ.1 hψ fun y hy => ?_
  refine h1 φ φ' φ'' a y ν hy.1 hν (HasDerivOn.mono hφ le_rfl hy.2)
    (HasDerivOn.mono hφ' le_rfl hy.2) ?_
    fun x hx => hlow x (Ioo_subset_Ioo le_rfl hy.2 hx)
  exact hmono.imp (fun h => h.mono (Ioo_subset_Ioo le_rfl hy.2))
    (fun h => h.mono (Ioo_subset_Ioo le_rfl hy.2))

theorem vdc2_of (h2 : VdC2PlainFacts) (hA : AmplitudeTransferFacts) : VdC2Statement := by
  intro φ φ' φ'' ψ ψ' a b μ p hab hμ hφ hφ' hlow hψ
  have hφp := HasDerivOn.add_linear hφ p
  refine hA _ ψ ψ' a b (8 / √μ) hab (by positivity) hφp.1 hψ fun y hy => ?_
  exact h2 _ _ φ'' a y μ hy.1 hμ (HasDerivOn.mono hφp le_rfl hy.2)
    (HasDerivOn.mono (HasDerivOn.add_const hφ' p) le_rfl hy.2)
    fun x hx => hlow x (Ioo_subset_Ioo le_rfl hy.2 hx)

theorem vdc3_of (h3 : VdC3PlainFacts) (hA : AmplitudeTransferFacts) : VdC3Statement := by
  intro φ φ' φ'' φ''' ψ ψ' a b μ p hab hμ hφ hφ' hφ'' hlow hψ
  have hφp := HasDerivOn.add_linear hφ p
  refine hA _ ψ ψ' a b (18 * μ ^ (-(1 : ℝ) / 3)) hab (by positivity) hφp.1 hψ fun y hy => ?_
  exact h3 _ _ φ'' φ''' a y μ hy.1 hμ (HasDerivOn.mono hφp le_rfl hy.2)
    (HasDerivOn.mono (HasDerivOn.add_const hφ' p) le_rfl hy.2)
    (HasDerivOn.mono hφ'' le_rfl hy.2) fun x hx => hlow x (Ioo_subset_Ioo le_rfl hy.2 hx)

end OscInt.VanDerCorput
