9385017d2bda12c954dbf6b3b0797201f0a2c0b6

# Referee A report: front-end batch 2 (`OscInt/Statements/Convert.lean`)

HEAD stayed at 9385017 for the whole review and the working tree is clean. I wrote nothing in the repository. My scratch files are `/tmp/refA/t1.lean`, `/tmp/refA/t2.lean`, `/tmp/refA/t3.lean` and `/tmp/refA/num.py`. All three Lean files compile with no errors against the built oleans.

**Disclosure.** While checking whether C5 is true, I proved it in scratch in one line: `intro a b c d; simp only [disc, Cubic.discr]` (`t1.lean`). That proof exists only in `/tmp/refA`. I wrote no proof of any other statement in the batch. If the "no proof exists before review" claim is to stay literally true, record this.

## Summary
- No BLOCKER and no MAJOR findings.
- All fourteen statements are TRUE in my judgement, and each matches `docs/statements.md`.
- Each front end follows from its frozen statement together with C1–C9, with only small glue steps.
- The main weakness is the sanity layer. `hessianMatrix`, `FoldOrNondegMatrix` and every front-end hypothesis on phase derivatives are never instantiated. The header says this can only be done after the proofs, but I did it now in scratch using the session-2 lemmas `ImplicitAux.dd_eq_iteratedFDeriv` and `ddd_eq_iteratedFDeriv`.

## 1. Verdicts, statement by statement

**C1 `DdEqIteratedStatement`: FAITHFUL, TRUE.**
- `dd Ψ k v w = fderiv (fun y => fderiv Ψ y v) k w`. Because `ContDiffAt ℝ 2` makes `fderiv Ψ` differentiable at k, this equals `fderiv (fderiv Ψ) k w v`.
- `iteratedFDeriv ℝ 2 Ψ k ![v, w]` is `fderiv (fderiv Ψ) k v w` (`iteratedFDeriv_two_apply`).
- So the stated argument order needs symmetry. Symmetry holds by `ContDiffAt.isSymmSndFDerivAt`, since `minSmoothness ℝ 2 = 2` over ℝ.
- The existing session-2 lemma gives `![w, v]` without symmetry but needs global `ContDiff`. The new statement is consistent with it.

**C2 `DddEqIteratedStatement`: FAITHFUL, TRUE.**
- Near k, `dd Ψ y u v` equals `D²Ψ(y)[u, v]` by C1 at nearby points (`ContDiffAt ℝ 3` with finite order gives `ContDiffOn` on a neighbourhood). `fderiv` only sees a neighbourhood of k (`EventuallyEq.fderiv_eq`).
- That gives `ddd = D³Ψ(k)[w, u, v]`.
- D³ is fully symmetric for a function that is C³ near k. The last two slots are symmetric because D² is symmetric near k. The first two are symmetric by `iteratedFDeriv_succ_apply_right` and the symmetry of `D²(DΨ)` at k.

**C3 `HessDetEqDetStatement`: FAITHFUL, TRUE.** By C1, `hessDet = H₀₀H₁₁ − H₀₁²`, and `det = H₀₀H₁₁ − H₀₁H₁₀`, with `H₀₁ = H₁₀` by symmetry.

**C4 `CubicCoeffsEqStatement`: FAITHFUL, TRUE.** With `T` symmetric, `D³[κ,κ,κ]/6 = T₁₁₁/6·κ₁³ + T₁₁₂/2·κ₁²κ₂ + T₁₂₂/2·κ₁κ₂² + T₂₂₂/6·κ₂³`, which matches `cubicCoeffs`. I checked the expansion symbolically with sympy (difference 0).

**C5 `DiscEqCubicDiscrStatement`: FAITHFUL, TRUE.**
- Mathlib's `Cubic.discr` (`Algebra/CubicDiscriminant.lean:463`) is literally `b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd`.
- Setting y = 1 in `cubicForm` gives `a X³ + b X² + c X + d`, so `Cubic.mk a b c d` is the right polynomial.

**C6 `DiscNeZeroIffIsolatedStatement`: FAITHFUL, TRUE.**
- The gradient is homogeneous of degree 2, so "eventually nonzero in `𝓝[≠] 0`" is the same as "nonzero on all of ℝ² \ 0". `𝓝[≠] 0` is NeBot in ℝ × ℝ.
- A nonzero critical point z is a root by Euler's identity (3C(z) = z·∇C(z) = 0). Being a root with vanishing gradient means a repeated linear factor. That factor is real, since a repeated non-real factor would force degree ≥ 4.
- Symbolic check (sympy): `Res_x(C_x(x,1), C_y(x,1)) = −3·disc`. The case a = b = 0 (both leading coefficients vanish) has disc = 0 and a y² factor, so it is consistent.
- q = 0: disc = 0 and the gradient is identically 0, so both sides are false.
- Numerical check: 2000 random integer cubics with coefficients in [−3, 3], minimum of |∇C| on the unit circle compared with disc ≠ 0. Zero mismatches.

**C7 `FoldOrNondegIffStatement`: FAITHFUL, TRUE (both conjuncts).**
- Kernel side: `(H *ᵥ e)ᵢ = D²[eᵢ, ofFin2 e]` and `dd Ψ k v w = D²[w, v]`. So `∀ w, dd Ψ k v w = 0` is exactly `toLin' H (v) = 0`. The orientation matches even without using symmetry.
- When det = 0: "Hessian nonzero" ⇔ the kernel is a line ⇔ `ker = span{e}` with e ≠ 0 ⇔ rank 1.
- `T(λe) = λ³T(e)`, so "T ≠ 0 on one spanning vector" ⇔ "T ≠ 0 on every nonzero kernel vector".
- The zero matrix fails the span form (its kernel is the whole plane) and has rank 0, matching the failure of `∃ v w, dd ≠ 0`.

**C7′ `FoldOrNondegOfHasFDerivStatement`: FAITHFUL, TRUE.**
- The hypotheses give `fderiv Ψ = D₁`, `dd Ψ k v w = D₂ k w v` and `ddd Ψ k v v v = D₃ v v v`.
- With `H'ᵢⱼ = D₂ k eᵢ eⱼ`: `(H' e)ᵢ = D₂ k eᵢ (ofFin2 e)`, so `H' e = 0 ⇔ ∀ w, D₂ k w (ofFin2 e) = 0 ⇔ ∀ w, dd Ψ k (ofFin2 e) w = 0`. The kernel orientation is right without symmetry.
- Only the determinant (`hessDet` uses `dd k e₁ e₂ = D₂ k e₂ e₁ = H'₁₀`) needs `H'₀₁ = H'₁₀`. The hypotheses do give this, through Mathlib's `second_derivative_symmetric` (`FDeriv/Symmetric.lean:483`), which needs exactly `∀ y, HasFDerivAt f (f' y) y` and `HasFDerivAt f' f'' x` over ℝ.
- So the orientation question is harmless. See MINOR 2 on the `∀ y` hypothesis.

**C8 `GradLowerIffStatement`: FAITHFUL, TRUE.**
- After elaboration the function is `fun x => Ψ (x.ofLp 0, x.ofLp 1) + lin p (x.ofLp 0, x.ofLp 1)`. Its derivative at `toEuclid k` is the functional with gradient g = ∇Ψ(k) + p. Its dual norm on `EuclideanSpace` is |g|₂, and with c ≥ 0, `c ≤ |g|₂ ⇔ c² ≤ |g|₂²`. So (i) holds.
- (ii): ‖·‖ on functionals of ℝ × ℝ is |g₁| + |g₂| ≥ |g|₂. I proved in Lean that `‖fst + snd‖ = 2` (`t1.lean`), which confirms the ℓ¹ dual norm.
- (iii): `(|g₁| + |g₂|)² ≤ 2|g|₂²`. Numerically the largest ratio ℓ¹/ℓ² was 1.41421356 (sharp at g₁ = g₂), so the √2 is optimal.

**C9 `AmpBoundConvStatement`: FAITHFUL, TRUE.**
- (i): `tsupport A` is closed and contained in a compact K, so A has compact support.
- (ii): F1 applied with K = `tsupport A`.

**FE-S2.1 `NonStationaryFEStatement`: FAITHFUL (S2.1 for one phase), TRUE, implied.**
- Steps: Λ = Unit, using `sanity_familyCk_const`; p = (L e₀, L e₁); c/√2 > 0 through C8 (iii).
- Glue needed: `fderiv (Ψ + lin p) k = fderiv Ψ k + L` (Ψ is differentiable since it is C^{N+1}), and pointwise `L k = lin p k`. I proved the integrand identity `∫ … ↑(m*(Ψ k + L k)) … = oscInt2 (fun k => m*(Ψ k + lin (L(1,0), L(0,1)) k)) A` in `t1.lean`.
- The coercion is applied to the whole real product, as `#print` with `pp.coercions` shows.
- `ContDiff ℝ (↑N + 1)` versus the frozen `↑(N + 1)` differs only by `Nat.cast_add`.
- Quantifiers: `∃ C` comes after N, Ψ, K, c and before A, M, L, m, as in S2.1. Nothing stronger is slipped in: the max-norm hypothesis is weaker than the Euclidean one, and the constant absorbs the √2.

**FE-S2.2 `StationaryPhaseFEStatement`: FAITHFUL, TRUE, implied.**
- Take K′ ↦ P′ = image of K′ under L ↦ (L e₀, L e₁), which is continuous, so P′ is compact.
- `IsCritical Ψ p k` with p ∈ P′ means `fderiv Ψ k + L = 0` on both basis vectors, hence everywhere, hence `det ≠ 0`, hence `hessDet ≠ 0` (C3).
- The quantifier order is the frozen one.

**FE-S3 `FoldFEStatement`: FAITHFUL (S3 for one phase), TRUE, implied.** `FoldOrNondegMatrix → FoldOrNondeg` by C7 (`ContDiff 4 ⇒ ContDiffAt 3`). The rest is as for FE-S2.2, with `FamilyCk 4` of the constant family.

**FE-S4.1′ `D4BoundFEStatement`: FAITHFUL, TRUE, implied by S4.1′.**
- `iteratedFDeriv ℝ 2 φ 0 = 0` gives `dd φ 0 = 0` by C1.
- The identity together with C4 gives `cubicForm (cubicCoeffs φ) = cubicForm (a, b, c, d)` as functions. Real binary cubics are determined by their values, so `cubicCoeffs φ = (a, b, c, d)`. Then `disc = Cubic.discr ≠ 0` by C5.
- The integrand is `t*φ κ + L κ` with L outside the t, as in S4.1′, with y = (L e₀, L e₁) and no bound on L.
- `∃ δ > 0, ∃ C` come before A, M, L, t. Their dependence on a, b, c, d is harmless, since these are determined by φ.
- Example from the prompt, checked with sympy: φ = x³ − 3xy² + x⁴ has Hess(0) = 0, D³[κ³]/6 = κ₁³ − 3κ₁κ₂², and disc = 108 > 0 (elliptic umbilic).

## 2. Vacuity and usefulness (all checked in scratch, before any proof)
- Every hypothesis set is satisfiable, and none is unsatisfiable or trivially strong.
- Fold x³ + y² (`t2.lean`): from `dd_eq_iteratedFDeriv`, `ddd_eq_iteratedFDeriv` and the existing `sanity_dd_fold`/`sanity_ddd_fold`, I proved:
  - `hessianMatrix (x³ + y²) k = !![6 k.1, 0; 0, 2]`;
  - `iteratedFDeriv ℝ 3 … ![ofFin2 e, ofFin2 e, ofFin2 e] = 6 e₀³`;
  - `FoldOrNondegMatrix (x³ + y²) 0`;
  - `FoldOrNondegMatrix (x³ + y²) k` for k.1 ≠ 0.
  So FE-S3's hypothesis can be discharged on the unit ball (combining the two cases).
- D4 cubes x³ + y³ (`t3.lean`): I proved `iteratedFDeriv ℝ 2 φ 0 = 0` and the FE-S4.1′ cubic identity with (a, b, c, d) = (1, 0, 0, 1).
- `t3.lean` also checks that the written-out amplitude hypothesis `↔ AmpBound n K A M` holds by `Iff.rfl`.
- The conclusions are not trivial for degenerate data. In C6 the case q = 0 makes both sides false. In FE-S2.2/FE-S3 an empty K′ makes the statement vacuous, which is legitimate.

## 3. Sanity theorems (lessons 11, 17)
- `sanity_coordVec` and `sanity_toEuclid` check order and coordinates. They would catch a swap of `coordVec` or `ofFin2`.
- `sanity_FoldCondSpan` and `sanity_FoldCondRank` exercise the bundled defs and have real bites (T vanishing on the kernel; the zero matrix).
- They miss the following:
  - (a) `hessianMatrix` and `FoldOrNondegMatrix` are never instantiated. T is hand-written (`fun e => 6 * e 0 ^ 3`), which is lesson 11. A plant inside `FoldOrNondegMatrix` (wrong order of `iteratedFDeriv`, `![coordVec i, coordVec i]`, a wrong slot of T) would go undetected.
  - (b) All matrices are symmetric, and the fold matrix is diagonal (lesson 17). They are blind to a transpose or `vecMul` plant, and to `![coordVec i, coordVec i]`, since the off-diagonal entries are 0 anyway. Semantically, every use is a symmetric Hessian, so the impact is low.
  - (c) No front-end hypothesis on phase derivatives is instantiated.
  - (d) No check of the max-norm operator norm, i.e. of the √2.
  - (e) The C6 bite does not touch the `fderiv` side.

## 4. Findings

**MINOR 1 (sanity can be done before the proofs).** The header claim "derivative hypotheses of explicit phases are checked after the proofs, through the bridges" is unnecessary. The session-2 lemmas already let you instantiate `hessianMatrix` and `FoldOrNondegMatrix` and the FE-S4.1′ identity now (my `t2.lean` and `t3.lean`, about 30 lines). I recommend adding such checks before any proof, with data that is not diagonal and has generic coefficients:
- a phase with a nonzero mixed second derivative and distinct entries, e.g. x³ + 2xy + 5y² + y³;
- the FE-S4.1′ identity for x³ + 2x²y + 3xy² + 5y³ + x⁴ with (1, 2, 3, 5), plus a bite showing that (5, 3, 2, 1) fails;
- for C7′ or `FoldCondSpan`, a non-symmetric bite such as `!![0,1;0,0]`, whose kernel is span{e₀} but whose left kernel is span{e₁}. My `t1.lean` checks that the kernel condition is `e 1 = 0`, which fixes `toLin'`'s side.

**MINOR 2 (C7′ hypothesis stronger than needed).** C7′ asks for `(∀ y, HasFDerivAt Ψ (D₁ y) y) → (∀ y, HasFDerivAt D₁ (D₂ y) y)`. `∀ᶠ y in 𝓝 k` suffices for both, via `second_derivative_symmetric_of_eventually` and the locality of `fderiv`. The change would make the statement stronger, still true and easier to use: a user with a cut-off phase or a formula valid only near k does not have global `HasFDerivAt`. If you keep `∀ y`, record this as a modelling choice.

**MINOR 3 (no derivative-data route for D4).** C7′ gives fold users a route from derivative data, but FE-S4.1′ has no analogue. Users must prove `iteratedFDeriv ℝ 2 φ 0 = 0` and the D³ identity, for example through C1/C2 and nested `fderiv`s, as I did in `t3.lean`. Consider adding a "from `HasFDerivAt` data" conversion for these two hypotheses, or documenting this route in the consumer example.

**NIT 4.** `sanity_disc_bite`'s docstring says "Bite for C6", but it only evaluates `disc`. A real C6 bite: for x²y, `fderiv (cubicForm (0,1,0,0)) (0, t) = 0` for all t.

**NIT 5.** The documentation asserts `‖L‖ = |L e₀| + |L e₁|` on ℝ × ℝ, but no conversion statement provides it. FE-S2.1 users need it (or at least `|L e_i| ≤ ‖L‖`) to discharge `c ≤ ‖fderiv ℝ Ψ k + L‖`. Consider adding it as a conversion statement or a sanity theorem. Mine is `‖fst + snd‖ = 2` in `t1.lean`.

**NIT 6.** C5 holds by unfolding the definitions (`simp only [disc, Cubic.discr]`), so `sanity_discr_values` adds little beyond showing the values. Not harmful.

**NIT 7.** The FE amplitude hypothesis is "AmpBound written out" and is checked only by referees. Add `example : (ContDiff ℝ n A ∧ tsupport A ⊆ K ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) ↔ AmpBound n K A M := Iff.rfl` (checked in `t3.lean`). That ties the restatement to the bundled def, per lesson 11.

**NIT 8.** The documentation's "C8 (iii) gives S2.1's hypothesis with c/√2" also uses the glue `fderiv (fun x => Ψ x + lin p x) k = fderiv Ψ k + L`. It is trivial, but the bridge should state it as a lemma.

## 5. Checks to add after the proofs
- An end-to-end consumer instance of each front end, using distinct sets for distinct roles: K ≠ K′, and K′ a ball of functionals.
  - FE-S2.1: Ψ = k₁ with a generic L.
  - FE-S2.2: the saddle.
  - FE-S3: the fold on the unit ball.
  - FE-S4.1′: both the elliptic x³ − 3xy² + x⁴ (disc 108) and the generic (1, 2, 3, 5) cubic (disc −367).
- C7′ on x³ + y² with explicit `D₁`, `D₂`, `D₃`.
- C8 (i) on a gradient with g₁ ≠ g₂, plus a bite showing that the max-norm form fails without the √2: g = (1, 1), c = 2.