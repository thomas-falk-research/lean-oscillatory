# Briefs for the proof agents of front-end batch 2 (API2)

Route: `docs/proof-API2.md`. Statements (frozen, stamped, reviewed FAITHFUL ×2): `OscInt/Statements/Convert.lean`,
mathematics in `docs/statements.md` ("Front end, batch 2").

## Common rules (every agent)
1. Repository `/home/user/lean-oscillatory`. Create ONLY your own file (named below). Do not edit, create or delete
   any other file in the repository; do not commit; do not run `lake build` of the library.
2. Check your file with `source ~/.elan/env; cd /home/user/lean-oscillatory; nice -n 10 lake env lean
   -DautoImplicit=false OscInt/API/<YourFile>.lean` — one Lean process at a time. It must compile with no errors and
   no `sorry` warning. Scratch experiments go under `/tmp/<your agent letter>/`, not in the repository.
3. Forbidden anywhere in your file (the guard rejects them): `sorry`, `admit`, `axiom`, `native_decide`,
   `implemented_by`, `unsafe`, `@[extern]`, `opaque`, `macro`, `elab`, `syntax`, `notation`, `run_cmd`, `run_tac`,
   `#eval`, `open Lean`, any `Lean.`-qualified name, `attribute`, `set_option` other than `set_option maxHeartbeats N
   in`, `private`. Write `∞`, never `⊤`, for C^∞. Keep each declaration under about 60 lines; helpers go in the
   namespace `OscInt.API.<Part>Aux` (e.g. `OscInt.API.DerivAux`).
4. Your theorems' types must be EXACTLY the statement constants named below (write `theorem name : XStatement := by
   …`). Never restate or weaken a statement. If you find a statement false or the route unworkable, STOP and report
   with a counterexample or the precise obstacle; do not work around it.
5. `#check` every Mathlib name before relying on it (lessons 1, 19 in `docs/lessons.md`): names drift. The
   session-2 lemmas `OscInt.StationaryPhase.ImplicitAux.dd_eq_iteratedFDeriv` and `ddd_eq_iteratedFDeriv`
   (`OscInt/StationaryPhase/Implicit.lean`, global `ContDiff`, arguments reversed) and the helpers next to them may
   be imported and reused.
6. Final message: the theorem names proved, the compile command's output (empty = success), the line count, anything
   you could not do and why.

## Agent D — `OscInt/API/ConvertDeriv.lean` (namespace `OscInt.API`)
Imports: `OscInt.Statements.Convert` (and Mathlib via it); you may import `OscInt.StationaryPhase.Implicit`.
Prove: `theorem dd_iteratedFDeriv : DdEqIteratedStatement`, `theorem ddd_iteratedFDeriv : DddEqIteratedStatement`,
`theorem hessDet_eq_det : HessDetEqDetStatement`, `theorem cubicCoeffs_eq : CubicCoeffsEqStatement`.
Route: `docs/proof-API2.md`, P-Deriv. Key names: `iteratedFDeriv_two_apply`, `iteratedFDeriv_succ_apply_left`,
`ContDiffAt.isSymmSndFDerivAt` (with `minSmoothness_of_isRCLikeNormedField` or the `minSmoothness ℝ 2 = 2`
lemma), `ContDiffAt.fderiv_right`, `ContDiffAt.eventually`, `Filter.EventuallyEq.fderiv_eq`, `fderiv_clm_apply`,
`Matrix.det_fin_two`. Pitfalls: `ContDiffAt ℝ 2` is only local — move to a neighbourhood with `ContDiffAt.eventually`
(finite order) before using C1 at nearby points; the symmetry of D³ needs two transpositions (route). For C4,
expanding `D³φ(0)[κ,κ,κ]` with `κ = κ.1 • (1,0) + κ.2 • (0,1)` is easiest through C2 and the linearity of `ddd` in
each argument after rewriting to the curried `fderiv (fderiv (fderiv φ)) 0` form; or through
`ContinuousMultilinearMap.map_add`/`map_smul` on `Function.update`.

## Agent Q — `OscInt/API/ConvertDisc.lean` (namespace `OscInt.API`)
Imports: `OscInt.Statements.Convert`.
Prove: `theorem disc_eq_cubic_discr : DiscEqCubicDiscrStatement`,
`theorem disc_ne_zero_iff_isolated : DiscNeZeroIffIsolatedStatement`.
Route: `docs/proof-API2.md`, P-Disc, with the two certificates and the three witnesses written out there (all checked
with sympy; `linear_combination` re-checks them). First compute `fderiv ℝ (cubicForm q) z` as an explicit functional
(`HasFDerivAt` of a polynomial in `z.1`, `z.2`; see `sanity_fd_cubes` in `OscInt/Statements/D4.lean` for the pattern),
so that `fderiv … z = 0 ↔ C_x(z) = 0 ∧ C_y(z) = 0`. Then: disc ≠ 0 ⇒ for every z ≠ 0 the derivative is nonzero
(certificates give disc·y³ = 0 and disc·x³ = 0 at a common zero); disc = 0 ⇒ a witness z₀ ≠ 0 with zero derivative,
then `t • z₀` for t → 0⁺ are critical points in every punctured neighbourhood (`Filter.Eventually`, `𝓝[≠] 0`:
use `Filter.Frequently` or `Metric.eventually_nhds_iff` / `eventually_nhdsWithin_iff`). Pitfalls: division in the
witness of the case g ≠ 0 — clear denominators by `field_simp` before `linear_combination`; the case analysis is on
g = b² − 3ac and on a.

## Agent F — `OscInt/API/ConvertFold.lean` (namespace `OscInt.API`)
Imports: `OscInt.Statements.Convert`.
Prove: the core `theorem OscInt.API.FoldAux.foldCore` with EXACTLY the statement in `docs/proof-API2.md` (P-Fold),
and `theorem foldOrNondeg_of_hasFDeriv : FoldOrNondegOfHasFDerivStatement`.
Route: core by linear algebra on 2×2 matrices: for symmetric H with det H = 0 and H ≠ 0 the kernel of
`Matrix.toLin' H` is a line (exhibit a spanning vector explicitly: if H₀₀ ≠ 0 or H₀₁ ≠ 0 take e = (−H₀₁, H₀₀), else
e = (−H₁₁, H₀₁) … check), rank one (`Matrix.rank`, `LinearMap.finrank_range_add_finrank_ker`, or direct), and
`T (c • e) = c³ T e`. Kernel orientation: `(H *ᵥ e) i = B (coordVec i) (ofFin2 e)`, so `H *ᵥ e = 0 ↔ ∀ w, B w (ofFin2 e)
= 0`. For C7′: from the hypotheses, `fderiv ℝ Ψ = D₁` (`HasFDerivAt.fderiv`), `dd Ψ y v w = D₂ y w v` for every y,
`ddd Ψ k v v v = D₃ v v v`; `D₂ k` is symmetric by `second_derivative_symmetric_of_eventually` (or
`second_derivative_symmetric`); apply the core with `B = (D₂ k)` (symmetric, so `D₂ k w v = D₂ k v w`) and
`T v = D₃ v v v` (cubic homogeneity by linearity). Pitfall: `FoldOrNondeg` writes `hessDet` with `dd … (1,0) (0,1) ^ 2`;
`coordVec 0 = (1, 0)` by `rfl`.

## Agent N — `OscInt/API/ConvertNorm.lean` (namespace `OscInt.API`)
Imports: `OscInt.Statements.Convert`, `OscInt.API` (for `OscInt.API.ampBoundOfContDiff`, F1).
Prove: `theorem gradLower_iff : GradLowerIffStatement`, `theorem ampBound_conv : AmpBoundConvStatement`, and the
helpers (exact statements, in namespace `OscInt.API.NormAux`):
`theorem norm_prod_functional (L : (ℝ × ℝ) →L[ℝ] ℝ) : ‖L‖ = |L (1, 0)| + |L (0, 1)|` and
`theorem fderiv_add_lin {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (h : DifferentiableAt ℝ Ψ k) (L : (ℝ × ℝ) →L[ℝ] ℝ) :
  fderiv ℝ (fun x => Ψ x + lin (L (1, 0), L (0, 1)) x) k = fderiv ℝ Ψ k + L`
and `theorem lin_apply_functional (L : (ℝ × ℝ) →L[ℝ] ℝ) (x : ℝ × ℝ) : lin (L (1, 0), L (0, 1)) x = L x`.
Route: `docs/proof-API2.md`, P-Norm. Norms: `ContinuousLinearMap.opNorm_le_bound`, `ContinuousLinearMap.le_opNorm`,
test vectors; on `EuclideanSpace ℝ (Fin 2)` use `EuclideanSpace.norm_eq`, `Fin.sum_univ_two`, Cauchy–Schwarz
(or `InnerProductSpace.toDual` norm). The Euclidean function in C8 composes `Ψ` with `x ↦ (x 0, x 1)`
(after elaboration `x.ofLp 0`): a continuous linear map; chain rule `HasFDerivAt.comp`. `toEuclid k` has coordinates
`k.1, k.2` (`sanity_toEuclid`). C9 (i): `HasCompactSupport.of_support_subset_isCompact` or
`IsCompact.of_isClosed_subset` with `isClosed_tsupport`; (ii) F1 with `K = tsupport A`.
