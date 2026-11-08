b71615cacaa5b250f625a4f55f0d1ee373f6bd4a

# Referee B: blind pre-proof statement review, batch GD (GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L)

Commit reviewed: `b71615cacaa5b250f625a4f55f0d1ee373f6bd4a` (HEAD checked at the start; the tree was not modified).
Files read: `docs/statements.md` (S2/S3, S4, front-end batches 1–3, batch GD in full), `OscInt/Statements/Global.lean`,
`Family.lean`, `Convert.lean` (definitions), `FrontEnd.lean` (`d4ClosedConstant`, F2), `OscInt/Front/GlobalSanity.lean`,
`docs/replay/2026-11-08-GD-sanity-plants.txt`, `docs/prereg/2026-11-08-P1-classify.md`,
`numerics/results-classify-2026-11-08.txt`, and `docs/lessons.md` entries 11, 12, 17, 24, 33.

Rule followed (lessons 24): I proved none of the eight statements, not even in scratch. The scratch work, all under
`/tmp/refB/`, was one Lean file that prints the elaborated statements and checks one `rfl` fact about the notation `∞`,
plus two standard-library Python scripts (numerics). One Lean process ran at a time.

## Summary

| Statement | vs docs | vs the classical result | TRUE? | Derivable from the frozen statements? |
|---|---|---|---|---|
| GD-C `GlobalDecayCritStatement` | FAITHFUL | FAITHFUL-WEAKER (cusps excluded, which the docs state) | TRUE | yes |
| GD `GlobalDecayStatement` | FAITHFUL | FAITHFUL-WEAKER (same) | TRUE | yes (GD-C argument plus FE-S2.1l for large `‖L‖`) |
| GD-F `GlobalFoldStatement` | FAITHFUL | FAITHFUL | TRUE | yes |
| GD-N `GlobalNondegStatement` | FAITHFUL | FAITHFUL | TRUE | yes |
| SH `SharpnessStatement` | FAITHFUL | FAITHFUL (elementary) | TRUE | elementary |
| T1 `TorusUnfoldStatement` | FAITHFUL | FAITHFUL | TRUE | elementary (product of 1D periodic partitions) |
| T6 `LatticeLaplacianDecayStatement` | FAITHFUL | FAITHFUL | TRUE (numerics below) | yes, T1 + GD |
| T6L `LatticeLaplacianLimitStatement` | FAITHFUL | FAITHFUL | TRUE (numerics below) | yes, T1 + F2 (S4.2 ∧ S4.4) + FE-S2.1 |

No BLOCKER and no MAJOR. There are four MINOR findings and six NITs (section 5). All four MINOR findings are about
sanity coverage, usability or documentation, not about the frozen text.

## 1. Statement by statement

### GD-C `GlobalDecayCritStatement`

**Quantifiers.** `∃ C` comes after Ψ, K, U, K′, D and their hypotheses, and before A, M, L, m. So C depends only on
the data, as the docs say. Uniformity over `L ∈ K′` is enforced by `L ∈ K'` in the inner hypotheses.

**Hypotheses.** They match the docs.
- K is compact, U is open, `K ⊆ U`, `↑D ⊆ U`, K′ is compact, and `ContDiffOn ℝ 4 Ψ U`.
- `ClassifiedCrit` requires `FoldOrNondegMatrix Ψ k` only for `k ∈ K`, `k ∉ D` and `fderiv ℝ Ψ k + L = 0` with
  `L ∈ K'`.
- Every `k₀ ∈ D` must satisfy `IsD4Point`.

**`IsD4Point`.** The elaborated form (checked with `#print`) is `iteratedFDeriv ℝ 2 Ψ k₀ = 0` together with
`∃ a b c d, (∀ x y, iteratedFDeriv ℝ 3 Ψ k₀ ![(x,y),(x,y),(x,y)] = 6 * (a x³ + b x²y + c xy² + d y³)) ∧
(Cubic.mk a b c d).discr ≠ 0`. This is FE-S4.1′L's hypothesis moved from 0 to k₀, with the same factor 6 and the same
`Cubic.mk` order. The iterated derivatives of `κ ↦ Ψ(k₀ + κ)` at 0 are those of Ψ at k₀, so the translation is
exact.

**TRUE, and derivable.** The argument:
1. Shrink δ until the balls `B̄(k₀, δ)`, `k₀ ∈ D`, are pairwise disjoint and each lies inside U. Here δ is FE-S4.1′L's
   radius for the translated phases `φ_{k₀}(κ) = Ψ(k₀ + κ)`, which are C⁴ on `U − k₀ ∋ 0`.
2. Take smooth cut-offs χ_{k₀} supported in `B̄(k₀, δ)` and equal to 1 on `B(k₀, δ/2)`.
3. On each piece χ_{k₀} A, translate and write `m(Ψ + L)(k₀ + κ) = mφ(κ) + (mL)(κ) + mL(k₀)`. The constant is a
   unimodular factor. FE-S4.1′L is uniform over all linear terms, so it covers `mL` for every L, not only `L ∈ K′`.
   Leibniz gives derivative bounds `C_χ M`.
4. The remainder `(1 − Σχ)A` is supported in `K₁ = K \ ⋃ B(k₀, δ/2)`, which is compact, lies inside U and does not meet
   D. On K₁, FE-S3l's classical hypothesis is exactly `ClassifiedCrit`'s first conjunct. FE-S3l gives `m^{−5/6}`, which
   is at most `m^{−2/3}` for `m ≥ 1`.

I found no step that fails. Two side remarks:
- The hypothesis "fold or nondegenerate at critical points near k₀" is not used by this argument, because FE-S4.1′L
  handles the whole ball. GD-C asks more near the D4 points than its proof needs. The extra demand is harmless,
  because it is automatic (next paragraph).
- Compactness of K′ is essential, not cosmetic. Take a sequence `L_n ∈ K′` converging to `L* ∉ K′`, where `Ψ + L*`
  has a critical point of type D5 (exponent 5/8 < 2/3) in K. Then the uniform bound fails, while each `Ψ + L_n` can
  still satisfy the classification. Dropping `IsCompact K'` would be a plant that matters, and it would go undetected.

**Is the near-D4 hypothesis satisfiable, or are there cusps?** It is satisfiable, and the docs' "CONJECTURED for every
homogeneous cubic" can be settled by a short argument (this is about the hypothesis, not a proof of the statement):
- Let f be a binary cubic with Disc ≠ 0, and let T = D³f, a constant symmetric trilinear form. At a point κ ≠ 0 the
  Hessian is `T[κ,·,·]`.
- It is nonzero: otherwise `∇f(κ) ∝ T[κ,κ,·] = 0`, so κ ≠ 0 is a critical point of f, which C6 excludes.
- So at a degenerate point κ ≠ 0 the Hessian has rank one, with kernel v.
- Suppose `T[v,v,v] = 0`.
  - If v ∥ κ, then `∇f(κ) = 0`, a contradiction.
  - Otherwise v, κ form a basis. `T[v,v,κ] = T[κ,v,v] = 0` and `T[v,v,v] = 0` give `T[v,v,·] = 0`, so `∇f(v) = 0`,
    again a contradiction.
- So every degenerate point of f other than 0 is a fold.
- For a C⁴ phase with that cubic part, `D²Ψ(k₀ + κ) = T[κ,·,·] + o(|κ|)` and `D³Ψ(k₀ + κ) = T + o(1)`. A compactness
  argument on directions then gives fold-or-nondegenerate in a punctured neighbourhood of k₀.

So near a D4 point no A₃ arises, and the hypothesis is never made false by the D4 point itself. A₃ points elsewhere
(not adjacent to D) are excluded, as documented. That is why the verdict against the classical uniform estimates
(Duistermaat, Karpushkin) is FAITHFUL-WEAKER: those cover every simple singularity. The rate 2/3 is the D4 rate and is
uniform over the deformations of D4 (A₃: 3/4, A₂: 5/6, A₁: 1), so the conclusion matches the classical result.

**Degenerate data.** If K = ∅, then `tsupport A ⊆ ∅` forces A = 0 and the conclusion holds trivially. If D = ∅, the
statement is FE-S3l with a weaker rate. Neither is a vacuity problem: the sanity data are non-degenerate.

### GD `GlobalDecayStatement`

**Quantifiers.** `∃ C` comes before A, M, L, m, with L unrestricted, which is what the docs say.

**Hypothesis.** `Classified Ψ K D` is pointwise: fold or nondegenerate at every point of `K \ D`. Nothing is lost by
asking this at every point instead of only at critical points. With L ranging over all functionals, every k is a
critical point of `Ψ + L` for `L = −fderiv ℝ Ψ k`. So "`ClassifiedCrit` for K′ = all L" is equivalent to `Classified`.

**TRUE, and derivable.**
1. `fderiv ℝ Ψ` is continuous on the open set U, hence bounded by some B on K.
2. For `‖L‖ ≥ R := 2B + 1` we have `‖fderiv ℝ Ψ k + L‖ ≥ 1` on K. FE-S2.1l with N = 1 applies: it needs
   `ContDiffOn ℝ 2 Ψ U`, which follows from C⁴; it needs `ContDiff ℝ 1 A`, which follows from C²; and it uses the bounds
   for `j ≤ 1`. It gives `C M / m ≤ C M m^{−2/3}`. Here M ≥ 0 follows from the j = 0 bound, and C can be taken ≥ 0.
3. For `‖L‖ ≤ R`, apply the GD-C argument with `K′ = closedBall 0 R` in the dual space. That ball is compact because
   the dual space is finite-dimensional.

The large-‖L‖ case is therefore not an obstacle.

**`↑D ⊆ U` is redundant.** A point of D in K is in U already, and a point of D outside K plays no role (K is closed, so
it stays a positive distance away). See N1.

### GD-F `GlobalFoldStatement` and GD-N `GlobalNondegStatement`

Both are FAITHFUL to the docs and TRUE.
- **GD-F:** FE-S3l with `K′ = closedBall 0 R` (its hypothesis holds pointwise), plus FE-S2.1l for `‖L‖ > R`.
- **GD-N:** FE-S2.2l with `(hessianMatrix Ψ k).det ≠ 0` at every point, plus FE-S2.1l.

The rates `m^{−5/6}` and `C * M / m` are as documented, and `∃ C` is placed correctly in both.

### SH `SharpnessStatement`

FAITHFUL and TRUE (elementary).
- **Lower bound.** Eventually `‖m^σ I(m)‖ ≥ ‖c‖/2`. For m > 0, `m^σ > 0` and `m^{−σ} = 1/m^σ`, which gives
  `‖c‖/2 · m^{−σ} ≤ ‖I m‖`.
- **No faster rate.** A bound `‖I m‖ ≤ C m^{−σ′}` with σ′ > σ would give `‖m^σ I m‖ ≤ C m^{σ − σ′} → 0`, contradicting
  `‖c‖ > 0`. This holds for every real C, including negative C.
- **Powers of non-positive bases.** For m ≤ 0, `Real.rpow` has junk values (and `(0:ℝ)^σ` in the sequence part), but
  every claim is eventual along `atTop`, so these values never matter.
- **Structure.** The two parts (real variable and ℕ-sequence) are stated separately, with `σ′` bound inside.

### T1 `TorusUnfoldStatement`

FAITHFUL and TRUE.
- **Smoothness index.** I checked in Lean that `(∞ : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞)` holds by `rfl` with
  `open scoped ContDiff`, and the file opens that scope. So `ContDiff ℝ ∞ η` means C^∞, not analytic. The lessons-12
  failure mode, where a compactly supported analytic η would be 0 and contradict `∫_box 1 = (2π)²`, is absent.
- **Construction.** Take `η(k) = ρ(k₁)ρ(k₂)`, where `ρ = χ / Σ_j χ(· + 2πj)` and χ is smooth, equal to 1 on [−π, π] and
  supported in [−3.9, 3.9].
- **Support.** The width 8 > 2π leaves room. `Metric.closedBall 0 4` on `ℝ × ℝ` is the max-norm square [−4, 4]².
- **Measure.** The box is `Icc ×ˢ Icc` with `volume` on `ℝ × ℝ`, the product Lebesgue measure.
- **Periodicity.** It is stated in each variable separately, as required, and continuity of g is required.

### T6 `LatticeLaplacianDecayStatement`

FAITHFUL to the docs and TRUE.
- **Kernel.** The integrand is `exp(i(t(cos k₁ + cos k₂) + x₁k₁ + x₂k₂))` with `x : ℤ × ℤ` cast to ℝ.
- **Quantifiers.** `∃ C` comes before t and x, so the bound is uniform over `x ∈ ℤ²` and `t ≥ 1`.
- **Sign and scale.** The sign of `x·k` is immaterial: k ↦ −k shows `K(t, −x) = K(t, x)`. The time scale 2 and the
  phase `e^{−4it}` change only constants, as disclosed.
- **Numerics.** The kernel factorises into 1D integrals `2π i^{x_j} J_{x_j}(t)`. My computation (periodic trapezoid,
  `/tmp/refB/num.py`) gives `sup_x |K(t,x)| t^{2/3}` of 23.1, 19.4, 18.5, 17.7, 18.1, 18.0 and 18.0 at
  t = 1, 3, 10, 30, 100, 300 and 1000. It is bounded, consistent with Landau's `sup_n |J_n(t)| ≲ t^{−1/3}`.
- **Derivation from T1 and GD.**
  1. Apply T1's identity to `g = integrand`, which is continuous and 2π-biperiodic because x is integral.
  2. Apply GD with Ψ = cos k₁ + cos k₂, `K = closedBall 0 4`, `U = univ` and D the four points (±π/2, ±π/2). In
     [−4, 4]² there are no other Hessian-zero points, since 3π/2 > 4.
  3. On the lines k₁ = ±π/2 the points are folds: kernel e₁, and `D³[e₁³] = sin k₁ = ±1`. Elsewhere `det H =
     cos k₁ cos k₂ ≠ 0`.
  4. At the four points, a = ±1/6 and d = ±1/6, with discr = −27a²d² ≠ 0.
  5. Use amplitude A = η (cast to ℂ), m = t and `L(k) = (x₁k₁ + x₂k₂)/t`.

  Every hypothesis can be discharged.
- **Use for dispersion.** With T1, this gives the ℓ¹ → ℓ^∞ dispersive bound for t ≥ 1. Negative times follow from
  `K(−t, x) = conj K(t, −x)`, and small times from the trivial bound `(2π)²`. That is what a dispersive estimate needs.

### T6L `LatticeLaplacianLimitStatement`

FAITHFUL and TRUE.
- **Casts.** The elaborated form is `↑(↑n ^ (2/3 : ℝ)) * (-1 : ℂ) ^ n * latticeKernel ↑n (↑n, ↑n)`. The time is
  `((n : ℕ) : ℝ)`, the lattice point is `((n : ℤ), (n : ℤ))` cast to ℝ inside the kernel, and the limit is
  `↑(d4ClosedConstant (-1/48 : ℝ))`.
- **D4 point.** The only critical point of `cos k₁ + cos k₂ + k₁ + k₂` in the box is (π/2, π/2), with phase value π
  (hence the factor (−1)ⁿ). The cubic part is `(κ₁³ + κ₂³)/6`, with disc = −27/36² = −1/48 < 0. The constant
  `Γ(1/3)²/(√3 · (1/48)^{1/6}) = Γ(1/3)² 48^{1/6}/√3 = 2^{2/3} Γ(1/3)²/3^{1/3}` agrees with the Bessel route
  `(−1)ⁿ K = (2π)² J_n(n)²`.
- **Independent numerics** (`/tmp/refB/num.py`). c* = 7.898993276562. Relative errors are 1.3e−3, 2.0e−4, 3.1e−5,
  4.8e−6 and 7.5e−7 at n = 10, 40, 160, 640 and 2560. The imaginary parts are ≤ 1e−12.
- **Derivation.** Use T1. The periodisation `Σ_j η(· + 2πj)` equals 1: it follows from T1's identity, since η is not
  named. In [−4, 4]² the only translate of (π/2, π/2) is itself, so `η(π/2, π/2) = 1`. Then apply F2 (S4.2 ∧ S4.4) to
  the translated phase, which has φ(0) = 0, ∇φ = 0 and D²φ = 0, with the amplitude cut off near k₀. Use FE-S2.1 with
  N = 1 on the rest, where the gradient is bounded below, for an `O(1/n)` remainder.

## 2. Derivability: summary

All eight statements follow from the frozen statements plus partition of unity, translation invariance of Lebesgue
measure and Leibniz bounds:
- GD-C: FE-S4.1′L + FE-S3l;
- GD, GD-F, GD-N: those and FE-S2.2l + FE-S2.1l;
- T6: T1 + GD;
- T6L: T1 + F2/S4.2/S4.4 + FE-S2.1;
- SH and T1: elementary.

No step fails. Nothing stronger than the argument gives has been slipped in. The one thing a user might want and
does not get is the rate `m^{−5/6}` or `m^{−1}` when D = ∅ in GD-C and GD; it is covered by GD-F and GD-N
(documented). A GD-C with D = ∅ and a fold rate (an FE-S3l analogue with the D exceptions) is simply FE-S3l.

Planted variants that would become FALSE, for the record:
- dropping `discr ≠ 0` from `IsD4Point`;
- dropping `IsCompact K'` in GD-C (the D5 sequence above);
- strengthening any rate (e.g. GD to 3/4: false for ellPhase by the D4 limit; T6 to 3/4: false by T6L + SH).

## 3. Vacuity and usefulness

- **cos k₁ + cos k₂** discharges GD on `closedBall 0 4` with four D4 points, as in the T6 derivation. The Hessian is
  diagonal and the fold checks are one line each.
- **arccos(a cos x + b cos y), |a| + |b| < 1.** The Hessian vanishes at (±π/2, ±π/2), since `ω''(0) = 0` and
  `D²(a cos x + b cos y) = 0` there. The cubic part is `[−(aκ₁³ + bκ₂³) + (aκ₁ + bκ₂)³]/6`. My discriminants for the six
  pre-registered (a, b) (−1.62e−4, −1.623e−4, −5.82e−5, −1.167e−4, −8.40e−5, −1.14e−6) agree to all printed digits
  with the pre-registration's output, which is an independent check of its closed-form derivatives. The fold condition
  on the degenerate curve is only numerically established (minfold ≥ 0.19). In Lean, a user must prove `T[v,v,v] ≠ 0`
  along a transcendental curve: possible but laborious (MINOR m3).
- **Hypotheses.** None is unsatisfiable. `Classified` and `ClassifiedCrit` are not trivially strong: near D4 points
  they are automatic (section 1).
- **Trivial conclusions.** With K = ∅ the conclusion is trivially true, which is acceptable. With D = ∅, GD is weaker
  than GD-F, also acceptable.
- **T6 with T1 and GD** says what the 2D lattice dispersive estimate needs: uniformity over x and over all t ≥ 1.

## 4. Sanity theorems and planted controls

The sanity theorems take the statement constant as a hypothesis and discharge its hypotheses on closed data, so they
test the frozen text (lessons 33). I checked the GD-C data by hand: the critical points of `E + 3x` are (0, ±1), in
`B̄(0, 1)`, with det H = −36. The ten plants are recorded as rejected, with matching unplanted copies accepted.

What they miss, with my estimate of what matters most:
1. **GD-C is not separated from GD (MINOR m1).** `globalDecayCrit_ell` uses ellPhase, which is nondegenerate at every
   point except the origin. A plant that replaces `ClassifiedCrit` by `Classified` in GD-C, or drops
   `fderiv ℝ Ψ k + L = 0 →` (both make the hypothesis harder), would still be discharged and go undetected. A
   separating datum: `x³ + y³` on `B̄(0, 2)` with `K′ = {−3·fst − 3·snd}` and D = ∅. The critical points (±1, ±1) are
   nondegenerate, and 0 is a non-critical non-fold point. The same datum also exercises D = ∅.
2. **D4 point only at the origin (MINOR m2, lessons 17).** Every D4 sanity datum has k₀ = 0. A plant that evaluates
   `IsD4Point`'s derivatives at 0 instead of k₀ (e.g. `iteratedFDeriv ℝ 2 Ψ 0`) is not detected. The same holds for
   `↑D ⊆ U ↦ ↑D ⊆ K`, since D = {0} ⊆ K. The text I reviewed uses k₀ correctly. A datum with a D4 point at k₀ ≠ 0
   fixes this, e.g. cos k₁ + cos k₂ at (π/2, π/2), or ellPhase translated.
3. **ellPhase has b = d = 0.** This is no problem for discr (it is invariant under order reversal anyway, as batch 2
   noted), but the coefficient order is pinned nowhere in this batch. It is inherited from FE-S4.1′L, so this is not a
   finding.
4. **Weakening plants that matter most, and are undetectable by design:**
   - dropping `discr ≠ 0` (makes GD false);
   - dropping `IsCompact K'` (makes GD-C false);
   - `C⁴ ↦ C³` (the route needs C⁴);
   - dropping `k ∉ D →` in the opposite direction, i.e. the exceptions not restricted to D4 points (e.g. D unrestricted:
     allowing arbitrary finitely many degenerate points, false for a D5 point);
   - T1: dropping continuity, or the support bound. Dropping the support bound is harmless for truth, but T6's
     derivation needs compact support.
   - T6L: only `c ≠ 0` is tested, not the value of the constant. That is pinned by numerics alone; my independent
     computation confirms it to 7.5e−7.
5. **T6 sanity is on the diagonal only.** It cannot catch a plant that restricts the uniformity to `x = (n, n)`. The
   docstring claims "the uniformity over x restricted (e.g. x = 0 only)" is detected. That is right for x = 0, but not
   for a restriction to the diagonal.

## 5. Findings

**BLOCKER:** none.

**MAJOR:** none.

**MINOR**
- **m1** (GlobalSanity, GD-C). `globalDecayCrit_ell` uses data that satisfy the pointwise `Classified`, so the sanity
  layer does not distinguish
  `(∀ L ∈ K', ∀ k ∈ K, k ∉ D → fderiv ℝ Ψ k + L = 0 → FoldOrNondegMatrix Ψ k)` from
  `(∀ k ∈ K, k ∉ D → FoldOrNondegMatrix Ψ k)`. Add a datum with a non-critical non-fold point in K (e.g. `x³ + y³`,
  `K = B̄(0, 2)`, `K′ = {−3 fst − 3 snd}`, `D = ∅`).
- **m2** (GlobalSanity, lessons 17). All D4 data have `k₀ = 0`, so `IsD4Point Ψ k₀`'s use of `k₀` in
  `iteratedFDeriv ℝ 2 Ψ k₀ = 0` and `iteratedFDeriv ℝ 3 Ψ k₀ ![(x, y), (x, y), (x, y)]` is not exercised. Use a D4
  point ≠ 0.
- **m3** (usability, docs). For arccos phases, discharging `Classified` on the support of η requires a Lean proof of
  the fold condition along a transcendental degenerate curve, for which there is only numeric evidence (minfold 0.19–0.51).
  It would help to state in the docs that this is the user's burden, or to plan a lemma.
- **m4** (docs, batch GD modelling choices). "CONJECTURED for every homogeneous cubic with nonzero discriminant": the
  short argument in section 1 proves it for exact cubics, and a compactness argument extends it to a punctured
  neighbourhood of a D4 point of any C⁴ phase. The docs could record this, as a referee remark and not a Lean fact.
  They could also say explicitly that GD-C's proof route does not use the hypothesis inside the D4 balls.

**NIT**
- **N1.** `(↑D : Set (ℝ × ℝ)) ⊆ U` in GD-C and GD is redundant: points of D ∩ K are in U already, and points of D \ K
  are irrelevant. It costs the user nothing.
- **N2.** The docstring of `L₁` in `GlobalSanity.lean` is garbled: "the critical points of `E + L₁` are
  `(±1/√… )`-free". It should say the critical points are (0, ±1).
- **N3.** The docstring of `latticeLaplacianDecay_diag` says the plant "uniformity over `x` restricted (e.g. `x = 0`
  only)" is detected. It is detected for x = 0, but not for a restriction to the diagonal.
- **N4.** GD-C and GD keep the rate 2/3 when D = ∅. This is documented as a choice and is fine; a one-line pointer to
  GD-F/GD-N in the GD-C docstring would help users.
- **N5.** T6L's constant is checked only numerically. The pre-registration and my independent check agree (7.5e−7 at
  n = 2560), and the closed forms through the Bessel route and `d4ClosedConstant (−1/48)` agree symbolically.
- **N6.** SH quantifies `σ′ > σ` with `C` unrestricted in sign. This is correct and slightly stronger than needed.

## Verdict

All eight statements are FAITHFUL to `docs/statements.md` and TRUE. All are derivable from the frozen statements
along the documented route. None is vacuous: the lattice Laplacian and the arccos phases satisfy the hypotheses, the
lattice phase easily. The remaining issues are sanity coverage (m1, m2) and documentation (m3, m4), which can be
addressed without re-freezing.
