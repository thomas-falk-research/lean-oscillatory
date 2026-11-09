c7282ab463cca3bf87bbca51341ce168f927152d

# Referee A: blind pre-proof statement review, batch A3 (S1.k, S5.1, S5.1′)

Summary: all three statements are FAITHFUL to `docs/statements.md` and TRUE. The definitions `DerivChain`, `IsA3Point` and `IsStableA3Point` say exactly what the mathematics says. I found no BLOCKER and no MAJOR issue. The findings are gaps in the sanity layer (MINOR) and documentation slips (NIT). The most important one: a plant that drops the kernel condition (i) from `IsA3Point` leaves every sanity theorem true, yet it admits an A4 point, which would make the planted S5.1′ false.

I did not prove any statement under review. My scratch Lean file only evaluates definitions and checks a planted definition on concrete data. The working tree was not modified (`git status` is clean).

Scratch files in /tmp/refA:
- /tmp/refA/lean/Defs.lean
- /tmp/refA/scripts/a3points.py
- /tmp/refA/scripts/s1k_and_plant.py
- /tmp/refA/scripts/n1grid.py
- /tmp/refA/scripts/n1beta.py
- the Python environment is /tmp/refA/venv, built from numerics/census/requirements.txt (sympy 1.14.0, mpmath 1.3.0, hash-pinned).

Lean was run one file at a time with `nice -n 10`. `OscInt/Front/CuspSanity.lean` recompiles from source with no errors, warnings or sorry.

## 1. Verdicts

**`DerivChain D k a b`**: FAITHFUL.
- For each j < k, `D j` is continuous on `Icc a b` and has derivative `D (j+1)` at every point of `Ioo a b`.
- `D k` is constrained only on `Ioo`, only as the derivative of `D (k-1)`. `D j` for j > k plays no role.
- This matches "D₀, …, D_k; endpoint continuity of D₀, …, D_{k−1}".

**S1.k (`VdCkStatement`)**: FAITHFUL to the docs. TRUE.
- `#print` with numeric types shows `(5 : ℝ) * (2 : ℝ) ^ (k - (1 : ℕ)) - 2`. Lean checks confirm:
  - the exponent is the natural number `k - 1` (exact for 2 ≤ k);
  - k = 4 gives 38 and k = 5 gives 78;
  - `μ ^ (-(1:ℝ)/(k:ℝ))` is `Real.rpow μ ((-1)/k)`;
  - at k = 4 it equals `(μ^(1/4))⁻¹`.
- Against Stein (Ch. VIII §1.2, Prop. 2 and Corollary):
  - Hypotheses are weaker than Stein's smooth φ in one respect: `D k` need not be continuous. Darboux still gives it a constant sign; the existing `SplitFacts` (P0) already covers this case.
  - Hypotheses are stronger in another: D₀, …, D_{k−1} must be continuous up to the endpoints. As in the S1 clarification, this is recovered by taking limits from subintervals.
  - The linear term changes only D₁, so for k ≥ 2 the uniformity in p is automatic.
- Exploratory check (40 random trials per k): the worst ratio |I|/(c_k μ^{−1/k}) was 0.33, 0.083, 0.041 and 0.020 for k = 2, 3, 4, 5. The phases were polynomials with |D_k| ≥ μ, random lower-order terms, random p and random intervals.

**`IsA3Point`**: FAITHFUL. It is exactly "A3 (corank 1, Milnor number μ = 3)" for C⁴ Ψ. Let H, T, Q be D², D³, D⁴ at k₀.
- **v = 0** makes (iv) read `H[w,w]·0 − 3·0² = 0`, so it is excluded. Hence v ≠ 0, H ≠ 0 and Hv = 0, which is rank one in ℝ².
- **w in the kernel** is excluded by (ii).
- **Any w = λv + βe with β ≠ 0** gives:
  - `H[w,w] = β²H[e,e]`;
  - `T[v,v,w] = βT[v,v,e]` (using (iii));
  - `g4(w) = β² g4(e)`, and v ↦ cv scales g4 by c⁴.
  - So both (iv) and (v) do not depend on the choice of (v, w), and the existential form equals the universal form.
- **Reduced quartic.** I re-derived it by hand: s(u) = −a21u²/(2h) + …, giving g(u) = (a40 − 3a21²/h)u⁴/24 + O(u⁵), so g4 = h·a40 − 3a21². This agrees with census check R1.
- **Argument order.** In `iteratedFDeriv ℝ n Ψ k₀ ![…]` the point is k₀ and the vector family is `![…] : Fin n → ℝ×ℝ`. For C^∞ Ψ the derivative is symmetric, so the order of entries is irrelevant.
- **Converse.** No non-A3 point satisfies the existential when Ψ is C⁴. For non-smooth Ψ, `iteratedFDeriv` returns junk values, but every statement assumes `ContDiff ℝ ∞`.

**`IsStableA3Point`**: FAITHFUL.
- The extra condition (v), `T[v,v,w] ≠ 0`, does not depend on (v, w), as shown above.
- It is equivalent to `d(det H)(k₀) ≠ 0`: the singular set of ∇φ is a smooth curve through k₀.
- Equivalently, linear perturbations form a versal unfolding of the A3 germ (the linear function s ≡ −(a21/2h)u² modulo the gradient ideal).

**S5.1 (`CuspBoundStatement`)**: FAITHFUL. TRUE. This is the classical uniform estimate (Duistermaat 1974) for a versally unfolded A3 point.
- `ContDiff ℝ ∞` is the smooth index: Lean checks `(∞ : WithTop ℕ∞) = ↑(⊤ : ℕ∞)` and `≠ ω`.
- `∃ δ > 0, ∃ C` comes before `A M y t`.
- y ∈ ℝ² is arbitrary and t ≥ 1.
- `t ^ (-(3:ℝ)/4)` is rpow.
- The ball is the max-norm `closedBall`, which changes constants only.

**S5.1′ (`CuspBoundGenStatement`)**: FAITHFUL. TRUE.
- Near a corank-1 point, every critical point of φ − L has Milnor number ≤ 3 (upper semicontinuity, A3 being 4-determined). So only A1, A2 and A3 occur.
- A direct route, below, proves it with C² amplitudes.

**Exploratory uniformity check** for x²y + y² with a Gaussian amplitude:
- grid: y₁ = αt^{1/4}, y₂ = βt^{1/2}, α, β ∈ [−2, 2] (81 points), extended to β ∈ [−6, 0];
- max of t^{3/4}|I| was 5.81, 6.32 and 6.49 at t = 10², 10³, 10⁴, always at (α, β) = (0, −2), an interior point after the extension;
- this is bounded and consistent with a Pearcey-type limit.

## 2. Derivability

**S1.k** follows by induction from existing pieces: P0 (`SplitFacts`), P3 (`vdc2Plain`), `amplitudeTransfer` and `HasDerivOn.add_linear`.
- Step: apply P0 to g = D_{k}, g′ = D_{k+1}. Take radius r = μ^{−1/(k+1)}, so that |D_k| ≥ μr = μ^{k/(k+1)} on the far pieces.
- This gives 2c_kμ^{−1/(k+1)} + 2r = (2c_k + 2)μ^{−1/(k+1)} = c_{k+1}μ^{−1/(k+1)}, which matches the stated constant.
- `vdCk_to_vdC2` and `vdCk_to_vdC3` compile, so S1.2 and S1.3 are the cases k = 2, 3.

**S5.1 by the anisotropic route** works.
- **FamilyCk 4.** Set Φ_ε(u,s) = ε⁻⁴[φ(εu, ε²s) − φ(0) − ∇φ(0)·(εu, ε²s)] in (v, w) coordinates, with Φ₀ = h s²/2 + (T/2)u²s + (Q/24)u⁴.
  - Each derivative ∂^{i,j} is ε^{i+2j−4}·∂^{i,j}φ(εu, ε²s), minus the removed linear part.
  - Weighted Taylor expansion gives joint continuity at ε = 0 for all i + j ≤ 4, using only φ ∈ C⁴ and a20 = a11 = a30 = 0.
  - So C⁴ already suffices; the doc's "C⁵ CONJECTURED" is conservative. C^∞ is more than enough.
- **E1 confirmed by hand.**
  - det D²P = h(Ts + Qu²/2) − T²u², the kernel vector is (h, −Tu), and T[v,v,v] = h²u(hQ − 3T²).
  - The degenerate curve meets u = 0 only at the origin, and at (0, s ≠ 0) det = hTs ≠ 0.
  - So every point of a compact weighted annulus is a fold or nondegenerate when T ≠ 0 and g4 ≠ 0.
  - This condition is open in (ε, κ), so it holds for ε ≤ ε₀.
- **Sum over scales.**
  - Each annulus contributes ε³·CM(tε⁴)^{−5/6} = CMt^{−5/6}ε^{−1/3}.
  - The sum over ε ≥ t^{−1/4} is ≲ t^{−3/4}, and the core region contributes t^{−3/4}.
  - S2.1 handles large rescaled p, which includes the term ε⁻⁴∇φ(0).
  - The rescaled amplitudes have C² norm ≤ C·M.

**S5.1′ by the Morse-with-parameters route** works with C² amplitudes. Coordinates are u along v, s along w.
- **Non-stationary in s.** If |p + φ_s(0)| > p₁ (p = y_w/t), integrate by parts once in s: O(M/t).
- **Stationary in s.** Otherwise s*(u, p) exists. Apply the Morse lemma in s with parameters (u, p).
  - Write the s-integral via Fourier: error ≤ C t^{−1/2}·t^{−1/2}∫|ξ||â| ≤ C M/t, uniformly in where s* lies.
  - The main term is t^{−1/2}∫e^{i(t g(u,p) + y_u u)} b(u) du with b ∈ C¹.
  - |∂⁴_u g| ≥ c holds for |u| ≤ δ, |p| ≤ p₁, by continuity from ∂⁴_u g(0,0) = g4/h ≠ 0.
  - S1.k with k = 4 then gives t^{−1/4}, so the total is t^{−3/4}.
- The order of choices is s₀, then p₁, then δ ≪ p₁.
- No step fails. The only obstacle is infrastructure: no Morse lemma with parameters exists in Mathlib or the repository. That leaves S5.1′ unproved, not false. The Hadamard-factor/IBP route used for S2/S3 may serve instead.
- As E2 shows, the anisotropic route itself fails for T = 0, which is why S5.1′ needs its own route.

## 3. Vacuity and usefulness

- **Hypotheses are satisfiable.** `gen_isStableA3` and `nonv_isA3` compile, and the S5.1/S5.1′ instances go through the statement constants.
- **Corpus points: both models satisfy `IsStableA3Point` after translation** (exact SymPy).
  - **Discrete Klein–Gordon** ω = √(5 − 2cos k₁ − 2cos k₂) at all four points (±π/2, ±π/2), with v = (−s₂, s₁), w = (1, 0):
    - Hv = 0, H[w,w] = −√5/25, T[v³] = 0, T[v,v,w] = ∓√5/5, g4 = −3/5;
    - the doc's value −√5/625 for its own v is reproduced.
  - **QWZ** at m = 3, ω = √(11 + 6(c₁ + c₂) + 2c₁c₂), at all four points (±a, ±a), a = arccos(−1/3):
    - det H = 0, T[v³] = 0, T[v,v,w] = ±128√130/53551875 (the doc's value), g4 = −19103744/8603409948046875 ≠ 0.
  - Both radicands are ≥ 1 on the torus (corner values 1, 5, 9), so both phases are C^∞ on ℝ² and the global `ContDiff ℝ ∞` hypothesis holds.
- **Local smoothness costs nothing.** If ω is smooth only near k₀, take a smooth global φ̃ that agrees with it near 0. Any δ′ ≤ δ is admissible, because `AmpBound` on a smaller ball implies it on `closedBall 0 δ`.
- **Not in this batch (as stated by the docs):**
  - a general point k₀ (`IsA3Point` is already stated at k₀; only the bounds are at 0);
  - compact families of phases;
  - the global assembly.
- **Advice for the global assembly.** Non-stable A3 points can form curves: for x⁴ + y², every (0, s₀) is an A3 point. So a "GD with cusps" built on S5.1′ should take a pointwise classification plus compactness, not a finite set of A3 points. Stable A3 points are isolated: in a punctured neighbourhood every point is a fold or nondegenerate, by the rescaling and E1 argument above, so a finite set fits S5.1.

## 4. Sanity theorems

**The bites fail exactly their target conditions.** I re-derived each one:

| Bite | Why it fails |
|---|---|
| `(y + x²/2)²` | v = (v₁, 0): g4 = 2w₂²·6v₁⁴ − 3·(2v₁²w₂)² = 0, while D⁴[e₁⁴] = 6 |
| `x³ + y²` | T[v³] = 6v₁³ |
| `x³ + y³` | H = 0 |
| `x² + y²` | forces v = 0 |
| `x⁴ + y²` | not stable, since T = 0 |

**Plants the sanity layer catches** (some sanity theorem becomes false or ill-typed):
- in S1.k: `k - 1 ↦ k`; exponent ↦ −1/2; `2 ≤ k ↦ 3 ≤ k`; `D k ↦ D 2`; `Ioo ↦ Icc`; dropping p; reversing the chain direction; `j < k ↦ j ≤ k`;
- in `IsA3Point`: dropping (ii) or (iii); 3 ↦ 2 in (iv); `T[v,v,w] ↦ T[v,w,w]` in (iv); straight-line quartic in place of g4;
- in S5.1: any change after `IsStableA3Point φ 0 →`, which the conditional sanity theorems restate textually;
- swapping `IsStableA3Point` and `IsA3Point`.

**Plants the sanity layer misses** are listed in section 5.

## 5. Findings

**MINOR 1 (kernel condition (i) is not separated by any datum).** The conjunct `(∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0)` can be dropped without any sanity theorem becoming false. Every bite is still rejected without it: x² + y² has no cubic or quartic part, and the trap, fold and rank-0 bites fail other conjuncts.
- Lean-checked in /tmp/refA/lean/Defs.lean:
  - the planted definition accepts the nondegenerate point x² + y² + x²y (`qNondegCubic`, with v = e₁, w = e₂, g4 = −12);
  - the real `IsA3Point` rejects it;
  - `x² + y²` stays rejected under the plant.
- SymPy: the A4 point (y + x²)² + x⁵ − 2y³ satisfies the plant with v = (1, 1), w = e₂ (Hv = (0, 2), T[v³] = 0, g4 = −144). Its reduced function is u⁵ + 2u⁶, so its decay is t^{−7/10} and the planted S5.1′ is false.
- Remedy: add the bite `x² + y² + x²y`, which fits the existing `quartic` machinery.

**MINOR 2 (all A3 data are axis-aligned).** Every datum uses v = e₁ and w = e₂ (lessons 17/38).
- A plant that fixes `v := (1,0)`, `w := (0,1)` instead of `∃ v w` leaves every sanity theorem true.
- That plant would exclude the KG and QWZ points, whose kernels are (1, ∓1).
- Remedy: add a datum with an oblique kernel, for example the generic quartic composed with (x, y) ↦ (x + y, y).

**MINOR 3 (no planted-control record for batch A3).** Lessons 33 says to run at least one planted copy per statement before the stamp. `docs/replay` has records for API3, GD, GDN, LE and VT, but none for A3, and commits 6c8fbe0 and 4811368 add none.

**NIT 4 (smoothness index).** `ContDiff ℝ ∞ φ ↦ ContDiff ℝ ω φ` (or `↦ ContDiff ℝ 4 φ`) is not caught.
- The data are polynomials, and `(quartic_contDiff _).of_le le_top` works at every index.
- `tools/src/bin/guard.rs` rejects only `⊤`.
- The frozen text is correct (`∞ ≠ ω`, Lean-checked). A non-analytic C^∞ datum, or a guard rule, would pin it.

**NIT 5 (non-stable bite has no cubic part).** The bite `x⁴ + y²` has T = 0, so a plant replacing (v) `T[v,v,w] ≠ 0` by `T[v,w,w] ≠ 0` passes (the generic datum has T[e₁,e₂,e₂] = 10).
- The plant cannot make S5.1 false, since S5.1′ covers those points, but it changes what "stable" means.
- Suggested bite: `x⁴ + y² + xy²` (A3, T[v,v,w] = 0, T[v,w,w] = 2).

**NIT 6 (S1.k constant pinned only at k = 2, 3).** Plants that agree there pass, for example `(5 : ℝ) * 2 ^ (k - 1) - 2 ↦ 10 * k - 12` or exponent `-(1)/k ↦ -(1)/(k^2 - 4k + 6)`. A k = 4 instance (38, μ^{−1/4}) would narrow this.

**NIT 7 (docs: S1.k proof sketch).** The sketch reads "split (a, b) where |D_k| ≥ δ from an interval of length ≤ 2δ … choose δ = μ^{−1/(k+1)}". This mixes threshold and radius.
- With threshold δ, the bad interval has length ≤ 2δ/μ and the choice must be δ = μ^{k/(k+1)}.
- With radius δ = μ^{−1/(k+1)}, the threshold is μδ.
- The recursion c_{k+1} = 2c_k + 2 is correct either way.

**NIT 8 (docs, modelling choice 2).** "CONJECTURED: C⁵ suffices" understates it: the weighted Taylor argument in section 2 gives `FamilyCk 4` for the rescaled family from C⁴. This is relevant to the later finite-smoothness front end, not to the frozen C^∞ statements.

No BLOCKER and no MAJOR. Statements: S1.k, S5.1 and S5.1′ are FAITHFUL and TRUE. Definitions: `DerivChain`, `IsA3Point` and `IsStableA3Point` are FAITHFUL.
