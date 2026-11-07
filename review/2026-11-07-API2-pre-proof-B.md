9385017d2bda12c954dbf6b3b0797201f0a2c0b6

# Referee B report: front-end batch 2 (Convert.lean), blind pre-proof review

## Summary
All fourteen statements are faithful to `docs/statements.md` and, as far as I can tell, true. Each front end follows from the frozen statement it fronts plus the conversions C1–C9, as the docs claim. I found no BLOCKER and no MAJOR. There are four MINOR and three NIT findings, mostly about usability and sanity coverage. I did not write any proofs of these statements, in scratch or elsewhere, so the statement-first order is intact. The truth arguments below are paper sketches, backed by:
- Lean `#check`/`#print` of the Mathlib lemmas they need;
- a check that `OscInt/Statements/Convert.lean` elaborates (`lake env lean`, no errors);
- numerical checks with sympy and numpy.

Scratch files: `/tmp/refB/checks.lean`, `/tmp/refB/checks2.lean`, `/tmp/refB/num.py`.

## 1. Verdicts on C1–C9 and C7′

**C1 `DdEqIteratedStatement`: FAITHFUL, TRUE.**
- By definition, `dd Ψ k v w = fderiv (fderiv Ψ) k w v`.
- Mathlib's `iteratedFDeriv_two_apply` gives `iteratedFDeriv ℝ 2 Ψ k m = fderiv (fderiv Ψ) k (m 0) (m 1)`, so `iteratedFDeriv ℝ 2 Ψ k ![v, w] = D(DΨ)(k) v w`.
- The stated order is therefore the transpose and needs symmetry at `k`. `ContDiffAt.isSymmSndFDerivAt` supplies it (`minSmoothness ℝ 2 = 2 ≤ 2`).
- `ContDiffAt ℝ 2` also makes `fderiv Ψ` differentiable at `k`, which is needed to commute "evaluate at `v`" with `fderiv`.
- This matches the disclosure: the existing `ImplicitAux` lemmas have the arguments in reverse order.

**C2 `DddEqIteratedStatement`: FAITHFUL, TRUE.**
- `ddd Ψ k u v w` is `D³(k)[w, v, u]` in the nested order, up to the near-`k` symmetry used in `dd`.
- Full symmetry of `D³Ψ(k)` follows from two facts: `D²Ψ` is symmetric on a neighbourhood (from `ContDiffAt 3`), and `iteratedFDeriv_succ_eq_comp_right` (unconditional) together with `isSymmSndFDerivAt` for the C² map `fderiv Ψ` near `k` gives symmetry in the first two slots.
- The docs correctly say the stated order uses this symmetry.

**C3 `HessDetEqDetStatement`: FAITHFUL, TRUE.** `det = H₀₀H₁₁ − H₀₁H₁₀`, while `hessDet` uses `dd e₁ e₂ ^ 2`. These agree by C1 plus symmetry.

**C4 `CubicCoeffsEqStatement`: FAITHFUL, TRUE.**
- Expanding `D³[κ,κ,κ]/6` with symmetric `T` gives `T₁₁₁/6 κ₁³ + T₁₁₂/2 κ₁²κ₂ + T₁₂₂/2 κ₁κ₂² + T₂₂₂/6 κ₂³`, which matches `cubicCoeffs`.
- Checked symbolically: for `x³+2x²y+3xy²+5y³+x⁴+7xy+11x`, the nested-`ddd` coefficients come out as (1, 2, 3, 5).

**C5 `DiscEqCubicDiscrStatement`: FAITHFUL, TRUE.**
- `#print Cubic.discr` shows `b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd`, the same polynomial as `disc` in the same order.
- Side remark: both are invariant under (a,b,c,d) ↦ (d,c,b,a) (checked with sympy), so a reversed `Cubic.mk d c b a` would also be true.

**C6 `DiscNeZeroIffIsolatedStatement`: FAITHFUL, TRUE.**
- Forward (disc ≠ 0 ⇒ isolated): if the gradient vanishes at some `z ≠ 0`, Euler's identity gives `C(z) = 0`, so `z` spans a repeated linear factor and disc = 0. This includes a double root at infinity, e.g. `a = b = 0` gives the factor `y²`.
- Backward (disc = 0 ⇒ not isolated): a real repeated factor is a line through 0 on which ∇C vanishes. Since ∇C is homogeneous of degree 2, it vanishes in every punctured neighbourhood. A repeated complex factor of a real cubic is real.
- q = 0: disc = 0, and the right side is false because `𝓝[≠] 0` is `NeBot` on `ℝ × ℝ`. The statement is correct there.
- Exhaustive sympy check over all 625 cubics with coefficients in {−2..2}: "disc ≠ 0" agrees exactly with "no common nonzero real zero of ∇C", 0 mismatches.

**C7 `FoldOrNondegIffStatement`: FAITHFUL, TRUE.**
- For a symmetric 2×2 matrix, "det = 0 and H ≠ 0" is the same as "rank 1", which is the same as "kernel is a line `span{e}`".
- `T(λe) = λ³T(e)`, so "nonzero on every nonzero kernel vector" is the same as "`T e ≠ 0`".
- When det = 0 and H = 0, both sides fail: the kernel is the whole plane, which is not `span{e}`, and the rank is 0.
- The kernel `{v | ∀ w, dd v w = 0}` agrees with `toLin'` (`H *ᵥ e = (D²[eᵢ, ofFin2 e])ᵢ`), using C1/C2 for `dd`/`ddd`.

**C7′ `FoldOrNondegOfHasFDerivStatement`: FAITHFUL, TRUE.** On the question of symmetry:
- From the hypotheses: `fderiv Ψ = D₁` everywhere, `dd Ψ y v w = D₂ y w v` for all `y`, and `ddd Ψ k v v v = D₃ v v v`. The diagonal needs no symmetry of `D₃`.
- The kernel needs no symmetry either. `FoldOrNondeg`'s kernel is `{v | ∀ w, D₂ k w v = 0}`, and `M *ᵥ e = (D₂ k eᵢ (ofFin2 e))ᵢ` is the same right kernel.
- "Hessian nonzero" is the same as `M ≠ 0`.
- Only the determinant needs `M₀₁ = M₁₀`, and the hypotheses do give it. Mathlib's `second_derivative_symmetric_of_eventually` (checked: `(∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) → HasFDerivAt f' f'' x → f'' v w = f'' w v`, over ℝ) applies with `f' = D₁` and `f'' = D₂ k`.
- So the iff holds.

**C8 `GradLowerIffStatement`: FAITHFUL, TRUE.**
- (i) The composite with `x ↦ (x.ofLp 0, x.ofLp 1)` is differentiable at `toEuclid k` (`sanity_toEuclid` pins the coordinates). Its Euclidean dual norm is `√(g₁²+g₂²)` with `gᵢ = ∂ᵢΨ(k)+pᵢ`, and with `c ≥ 0`, `c ≤ √S ⟺ c² ≤ S`.
- (ii) The max-norm dual norm is `|g₁|+|g₂| ≥ √(g₁²+g₂²)`.
- (iii) `(|g₁|+|g₂|)² ≤ 2(g₁²+g₂²)`.
- The hypothesis `0 ≤ c` is necessary for (iii). Counterexample without it: c = −10, g = 0.
- Numerically, the max-norm operator norm equals |a|+|b| for random functionals, and the ratio to the 2-norm stays ≤ √2.

**C9 `AmpBoundConvStatement`: FAITHFUL, TRUE.** (i) A closed `tsupport` inside a compact `K` gives `HasCompactSupport`. (ii) is F1 with `K = tsupport A`.

## 2. Front ends

**FE-S2.1: FAITHFUL (FAITHFUL-WEAKER by design: one phase, no family). It follows from S2.1 + C8(iii).** The derivation:
- Take Λ = Unit, so `FamilyCk (N+1)` comes from `ContDiff`, as in `sanity_familyCk_const`.
- Apply S2.1 with constant `c/√2 > 0`.
- For `L`, put `p = (L e₀, L e₁)`; then `lin p k = L k` pointwise, and `fderiv (Ψ + lin p) k = fderiv Ψ k + L` because Ψ is differentiable (N+1 ≥ 1).
- The integrand matches `oscInt2` exactly after `funext`.
- Quantifiers: `∃ C` comes after N, Ψ, K, c and before A, M, L, m, the same as S2.1. Uniformity over all `L` (not only those in a compact set) is preserved.
- `j = 0` forces `M ≥ 0`, so negative `M` cannot trivialise the conclusion. Nothing stronger is slipped in.

**FE-S2.2: FAITHFUL. It follows from S2.2 + C3.**
- Set `K'' = {(L e₀, L e₁) | L ∈ K'}`. This set is compact, since evaluation is continuous for the operator-norm topology.
- `IsCritical Ψ p k ⟺ fderiv Ψ k + L = 0`, since a functional is zero iff it vanishes on the basis.
- C3 converts `hessDet` to the determinant.
- Quantifier order is as in S2.2.

**FE-S3: FAITHFUL (one phase). It follows from S3 (Λ = Unit) + C7**, using `ContDiffAt 3` from `ContDiff 4`.

**FE-S4.1′: FAITHFUL. It follows from S4.1′ + C1 + C4 + C5.**
- C1 turns `iteratedFDeriv ℝ 2 φ 0 = 0` into `∀ v w, dd φ 0 v w = 0`.
- C4 plus the user's identity give `cubicForm (cubicCoeffs φ) = (a,b,c,d)` as functions, hence equal coefficients (evaluate at four points). C5 then gives `disc (cubicCoeffs φ) = (Cubic.mk a b c d).discr`.
- `lin (L e₀, L e₁) = L`.
- `∃ δ > 0, ∃ C` comes before A, M, L, t, as in S4.1′. The ball is the max-norm ball, as frozen.
- Example: for x³−3xy²+x⁴ the Hessian at 0 is 0, `D³φ(0)[k³] = 6(k₁³ − 3k₁k₂²)`, so (a,b,c,d) = (1,0,−3,0) and disc = 108 ≠ 0. The hypotheses are satisfiable.

## 3. Vacuity and usefulness
- No hypothesis is unsatisfiable. All of the following are dischargeable in principle through nested `fderiv` computations (the `sanity_dd_fold` pattern) followed by C1/C2/C3/C7:
  - fold x³+y² on the unit ball (FE-S3);
  - saddle x²−y² (FE-S2.2);
  - Ψ = k₁ with L = 0 (FE-S2.1);
  - x³−3xy²+x⁴ (FE-S4.1′).
- Degenerate data only make conclusions trivially true in the expected ways (K' = ∅, c = 0 in C8). None of these hides a problem.
- C7′ asks for `HasFDerivAt` at every point. That is stronger than the proof needs, but it is satisfiable for polynomials. See MINOR 2.

## 4. Sanity theorems
- They use the statement's own definitions (`FoldCondSpan`, `FoldCondRank`, `coordVec`, `ofFin2`, `toEuclid`, `disc`, `Cubic.discr`), in line with lesson 11.
- They include bites (`T` vanishing on the kernel, zero matrix, x²y with disc 0), in line with lesson 17. The coefficients (1, 2, 3, 5) are generic.
- What they miss:
  - `hessianMatrix`, `FoldOrNondegMatrix` and `cubicForm`'s derivative are never exercised.
  - Every matrix witness is diagonal and symmetric. That makes them blind to:
    - right vs left kernel (`toLin' H` vs `toLin' Hᵀ`);
    - an i/j swap in `hessianMatrix`;
    - an `e 0`/`e 1` swap inside `FoldOrNondegMatrix`'s `T`, since `T` is only ever passed directly.
  - The swaps of `toLin'` and `hessianMatrix` are harmless in substance, because every Hessian here is symmetric (C7′ included, via Mathlib's symmetry lemma). They are still unpinned.
  - Nothing tests that `‖L‖` on `ℝ × ℝ` is |a|+|b| rather than the 2-norm, which is the √2 direction in C8.
  - `sanity_discr_values` is blind to coefficient reversal. This is harmless because `disc` is reversal-invariant.

## 5. Findings
No BLOCKER. No MAJOR.

**MINOR 1 (usefulness).** C7′ is the only conversion from explicit derivative data. FE-S2.2's `(hessianMatrix Ψ k).det ≠ 0` and FE-S4.1′'s `iteratedFDeriv ℝ 2 φ 0 = 0` / `iteratedFDeriv ℝ 3 φ 0 ![(x, y), (x, y), (x, y)] = 6 * (...)` have no `HasFDerivAt`-data analogue, so users must go through nested `fderiv` and C1/C2. For FE-S3, a user needs C7′ and then C7 (two steps) to reach `FoldOrNondegMatrix`.
- Suggestion: in a later batch, add "C1′/C2′": from the C7′ hypotheses, `iteratedFDeriv ℝ 2 Ψ k ![v, w] = D₂ k v w` and `iteratedFDeriv ℝ 3 Ψ k ![u, v, w] = D₃ u v w` under a smoothness hypothesis. Also add a variant of C7′ that concludes `FoldOrNondegMatrix` directly.

**MINOR 2.** In C7′ the hypotheses `(∀ y, HasFDerivAt Ψ (D₁ y) y) → (∀ y, HasFDerivAt D₁ (D₂ y) y)` could be `∀ᶠ y in 𝓝 k` at no cost: the proof is local, and the symmetry lemma takes `∀ᶠ`. This matters for phases that were cut off to a global C⁴ function. It is optional, since the statement is true as written.

**MINOR 3 (sanity, lesson 17).** `sanity_ker_fold`, `sanity_FoldCondSpan`, `sanity_rank_fold` and `sanity_FoldCondRank` use only `!![0, 0; 0, 2]`. Add a non-symmetric rank-one witness that pins `toLin'` as the right kernel: `!![(1:ℝ), 2; 3, 6]` has right kernel `span{![2, -1]}` and left kernel `span{![3, -1]}`. Pair it with an asymmetric `T`, e.g. `T e = e 0 ^ 3 + 2 * e 0 ^ 2 * e 1` (nonzero at (2, −1), zero at (0, 1)).

**MINOR 4 (post-proof non-vacuity checks to add, through the bridges).**
- `hessianMatrix (x³+y²) 0 = !![0, 0; 0, 2]`, and one Hessian with nonzero off-diagonal entries, e.g. x² + 3xy + 5y² ↦ `!![2, 3; 3, 10]`, det 11.
- `FoldOrNondegMatrix` for the fold at every k. Bite: y² + x⁴ at 0 (third derivative vanishes on the kernel).
- FE-S4.1′ hypotheses for x³ + 2x²y + 3xy² + 5y³ + x⁴ (generic, disc −367) and for x³ − 3xy² + x⁴ (elliptic, disc 108). Bite: x²y + x⁴ (disc 0).
- C6 bite: ∇(x²y) vanishes at (t, 0).
- C8 with gradient (3, 4): max-dual norm 7, Euclidean 5.
- C7′ instantiated with explicit D₁, D₂, D₃ for x³+y² at 0.
- FE-S2.1 gradient hypothesis for Ψ = k₁ with L = 0, plus a bite with L = −fst (gradient 0).

**NIT 1.** In FE-S2.1, `ContDiff ℝ (N + 1) Ψ` elaborates to `ContDiff ℝ (↑N + 1) Ψ`, while S2.1's `FamilyCk (N + 1)` gives `ContDiff ℝ ↑(N + 1)`. Likewise `ContDiff ℝ 4` vs `↑(4 : ℕ)`. The bridge needs a cast rewrite. This is harmless.

**NIT 2.** `sanity_discr_values`/`sanity_disc_bite` cannot detect a coefficient reversal (a,b,c,d) ↔ (d,c,b,a), because `disc` and `Cubic.discr` are invariant under it. Any such plant would yield a true statement, so this is harmless. Worth one sentence in the docs. The ordering of a, b, c, d in the FE-S4.1′ identity is pinned only by a derivative-level check with a non-palindromic cubic (see MINOR 4).

**NIT 3.** The docstring "C7′ `FoldOrNondeg` from derivative data" and the definition name `...OfHasFDeriv...` suggest a one-way implication; the statement is an iff. A wording point only.