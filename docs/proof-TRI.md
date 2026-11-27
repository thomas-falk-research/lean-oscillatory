<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Proof route for batch TRI (TRI-K, TRI-X, TRI-W, TRI-Q)

Written by the lead on 2026-11-27, after the answers to the blind pre-proof reviews were stamped
(`stamps/20261127T070956Z-e692d7e55078`). This is a route for Lean, not a new proof. The mathematics is the external
derivation checked in `review/2026-11-26-A5-handoff-answers.md` (K1, K3). Every identity below was re-checked by the
lead in exact SymPy, in the coordinates the Lean statements use; the scripts are in the lead's scratch. The route
differs from the paper in two places:
- the A5 witness avoids square roots and series (section 5);
- the bridge from `IsA5Point` to the jet invariants is a separate lemma (section 4).

## 0. Notation

- `Ψ = triPhase α`, `k = (x, y)`. Write `D²[a, b]`, `D³[a, b, c]`, `D⁴[a, b, c, d]` for
  `iteratedFDeriv ℝ n Ψ k ![…]`.
- Explicit forms, the sanity layer's `triD2_mixed`, `triD3_mixed` and `triD4`, re-proved in a proof module:
  - `D²[a, b] = −a₁b₁ cos x − a₂b₂ cos y − α(a₁ + a₂)(b₁ + b₂) cos(x + y)`;
  - `D³[a, a, b] = a₁²b₁ sin x + a₂²b₂ sin y + α(a₁ + a₂)²(b₁ + b₂) sin(x + y)`;
  - `D⁴[a⁴] = a₁⁴ cos x + a₂⁴ cos y + α(a₁ + a₂)⁴ cos(x + y)`.
- `fderiv ℝ Ψ k a = −a₁ sin x − a₂ sin y − α(a₁ + a₂) sin(x + y)`.
- Quartic invariant: `Qinv(v, w) = D²[w, w] D⁴[v⁴] − 3 (D³[v, v, w])²`, the expression of `IsA3Point`.
- Half-angle variables: `s = (x + y)/2`, `σ = (x − y)/2`, and `c = cos s`, `l = sin s`, `d = cos σ`, `m = sin σ`,
  with `c² + l² = 1` and `d² + m² = 1`. Then:
  - `cos x = cd − lm`, `sin x = ld + cm`;
  - `cos y = cd + lm`, `sin y = ld − cm`;
  - `cos(x + y) = 2c² − 1`, `sin(x + y) = 2lc`.
- `P = c²`, `Q = d²`, and
  - `D = P + Q − 1 + 2αcd(2P − 1)`;
  - `R = 8αc³d³ + 2PQ − P − 2Q² + Q + 1`;
  - `E = 2P² + 8PQ² − 4PQ − 3P − 2Q² + Q + 1`;
  - `G = 2P²Q − P² − 2PQ + 2P + 2Q³ − Q² − 1`.
- `V = (cd + lm, cd − lm)` and `W = (1, −1)`, as vectors in the (x, y) coordinates.

## 1. Exact identities (polynomial in c, l, d, m, α modulo the two circle relations)

Checked in SymPy as stated, in the (x, y) coordinates:
- (I1) `hessDet = D²[e₁, e₁] D²[e₂, e₂] − D²[e₁, e₂]² = D`. This is in (x, y); the paper's `4D` is in (s, σ).
- (I2) `D²[V, e₁] = D²[V, e₂] = −D`. So V is in the kernel when D = 0.
- (I3) `D³[V, V, V] = 2lc · R`.
- (I4) `(2P − 1)R − 4PQ·D + E = 0`.
- (I5) `2cd · D⁴[V⁴] + 3 (D³[V, V, W])² = −12P·G + 16P²Q²·D`, and `D²[W, W] = −2cd`. So on D = 0,
  `Qinv(V, W) = 12P·G`.
- (I6) `2G − (2Q − 1)E = B·P − N` and `B²·E(P, Q) − 8Q²(Q − 1)(2Q − 1)F(Q) = (BP − N)·(…)`, where
  - `B = 16Q²(1 − Q) + 1 − 2Q`;
  - `N = (1 − Q)(8Q² + 2Q + 1)`;
  - `F = 32Q⁴ − 16Q³ − 8Q² − 8Q + 1`.

  In SymPy the factor `(…)` is
  `−32PQ³ + 32PQ² − 4PQ + 2P − 128Q⁵ + 192Q⁴ − 48Q³ − 20Q² + 4Q − 1`, with remainder 0. Write the second identity as
  `linear_combination`: it is the substitution `P = N/B` cleared of denominators.
- (I7) Rational certificate: with `h = 19/20 − Q` and `k = Q − 1/2`, `h + k = 9/20` and
  `(h + k)⁴ F = −5h⁴ − (127/5)h³k − (1074/25)h²k² − (12673/500)hk³ − (7369/5000)k⁴`.
  So F < 0 on [1/2, 19/20].
- Boundary cases, checked in SymPy at every sign choice:
  - c = 0 (then D = 0 forces m = 0, d² = 1): the kernel is spanned by `(1, −1)`, the cubic along it is 0,
    `D²[(1, 1), (1, 1)] = 4α` and `Qinv((1, −1), (1, 1)) = −12`.
  - d = 0 (then c² = 1, l = 0): the kernel is spanned by `(1, −1)`, and `D³[(1, −1)³] = ±2 ≠ 0`.
  - l = 0 (P = 1): `G = Q²(2Q − 1)`.

## 2. Algebraic classification (part P-alg)

Let α ≠ 0 and k ∈ ℝ².
1. **The Hessian is not zero.** If all three entries vanish, then `α cos(x + y) = 0`, so cos(x + y) = 0, and then
   cos x = cos y = 0. That is impossible: `cos(x + y) = cos x cos y − sin x sin y = −sin x sin y`, which is ±1.
2. **D ≠ 0:** `FoldOrNondeg` (first disjunct; `hessDet` from `dd`, conversion C1).
3. **D = 0, d = 0:** `FoldOrNondeg` (second disjunct). Every nonzero kernel vector is a multiple of `(1, −1)`, and
   the cubic along it is `±2λ³ ≠ 0`.
4. **D = 0, c = 0:** `IsA3Point` with v = (1, −1) and w = (1, 1) (quartic −12).
5. **D = 0, cd ≠ 0.** Then V ≠ 0, and {V, W} is a basis (determinant `−2cd`). Every nonzero kernel vector is
   `λV` with λ ≠ 0. The cubic along it is `λ³ · 2lcR`.
   - (a) **2lcR ≠ 0:** `FoldOrNondeg`.
   - (b) **l ≠ 0, R = 0:** E = 0 by (I4). If G = 0 as well, then (section 3) P and Q satisfy E = G = 0 with
     0 < P < 1 and 0 < Q ≤ 1, which is impossible. So G ≠ 0 and `IsA3Point` with V, W (`Qinv = 12PG ≠ 0`).
   - (c) **l = 0:** P = 1 and `Qinv(V, W) = 12Q²(2Q − 1)`.
     - If 2Q ≠ 1: `IsA3Point`.
     - If 2Q = 1: the **A5 locus**.
       - D = 0 gives `Q + 2αcd = 0`. With d ≠ 0 this is `d = −2αc`, so `4α² = Q = 1/2` and `|α| = a*`.
       - `cos x = cd − lm = cd = −2αc² = −2α`.
       - `x + y = 2s` with sin s = 0, so `x + y ∈ 2πℤ` (`Real.sin_eq_zero_iff`).
       - `Real.cos_eq_cos_iff` with `cos(arccos(−2α)) = −2α`, valid since `|2α| ≤ 1`, gives
         `x = ±arccos(−2α) + 2πj₁` and `y = ∓arccos(−2α) + 2πj₂`. This is TRI-X's locus.

**The invariance step**, needed by TRI-X. Given any v ≠ 0 in the kernel with `D³[v³] = 0` and any w with
`D²[w, w] ≠ 0`:
- write `w = μW + νv` (W fixed so that {v, W} is a basis);
- then `D²[w, w] = μ²D²[W, W]` (so μ ≠ 0), `D³[v, v, w] = μD³[v, v, W]` and `Qinv(v, w) = μ²Qinv(v, W)`;
- with `v = λV`, `Qinv(v, W) = λ⁴Qinv(V, W)`.

So `Qinv(v, w) = 0` iff `Qinv(V, W) = 0`. With the explicit forms of section 0 this is `linear_combination`; no
symmetry of `iteratedFDeriv` beyond those forms is needed.

Interfaces:
- `TriAlgClassify α k`: for α ≠ 0, `FoldOrNondeg ∨ IsA3Point ∨ (|α| = a* ∧ InLocus α k)`.
- `TriAlgA5 α k`: for α ≠ 0, if v ≠ 0 is in the kernel, `D³[v³] = 0`, `D²[w, w] ≠ 0` and `Qinv(v, w) = 0`, then
  `|α| = a* ∧ InLocus α k`.
- `InLocus α k` is TRI-X's disjunction with integer shifts.

## 3. No A4 or worse off the symmetry line (lemma P-EG)

Pure real algebra. If 0 < P < 1, 0 < Q ≤ 1, E = 0 and G = 0, then False.
1. **Q = 1:** E = P(2P + 1) > 0.
2. **Q = 1/2:** G = P − 1 < 0.
3. **Otherwise:** (I6) gives BP = N, and N > 0 for 0 < Q < 1.
   - So B > 0. Then `B²E = 8Q²(Q − 1)(2Q − 1)F` (no division), so with E = 0 and Q ∉ {1/2, 1}, F = 0.
   - **0 < Q < 1/2:** `N − B = Q(4Q − 3)(2Q − 1) > 0`, so P = N/B > 1, a contradiction.
   - **19/20 ≤ Q < 1:** `B ≤ 16(1 − Q) + 1 − 2Q ≤ −1/10`, a contradiction with B > 0. The first inequality uses
     `Q² ≤ 1`.
   - **1/2 < Q < 19/20:** F < 0 by (I7), a contradiction with F = 0.

Expected tactics: `nlinarith` or `positivity` per case, and `linear_combination` for (I6).

## 4. The bridge from `IsA5Point` to the jets (part P-bridge)

General lemma, for any `Ψ : ℝ × ℝ → ℝ` with `ContDiff ℝ ∞ Ψ`, `k₀`, v in the kernel at k₀, `D²[w, w] ≠ 0`, ε > 0,
and `ReducedCurve Ψ k₀ v w ε h`. With `g = reducedFn Ψ k₀ v w h`:
- `iteratedDeriv 1 g 0 = 0` and `iteratedDeriv 2 g 0 = 0`;
- `iteratedDeriv 3 g 0 = D³[v, v, v]`;
- `iteratedDeriv 4 g 0 = D⁴[v⁴] − 3 (D³[v, v, w])² / D²[w, w]`.

Route. Write `γ(u) = k₀ + u v + h(u) w`, so `γ′ = v + h′w`, and let `L = fderiv Ψ k₀`.
1. `g(u) = Ψ(γ u) − L(γ u − k₀)`, so
   `g′(u) = DΨ(γ u)(v + h′(u)w) − L(v + h′(u)w)`.
2. ReducedCurve gives `DΨ(γ u)w = Lw` on |u| < ε. Hence `g′(u) = DΨ(γ u)v − Lv` on |u| < ε, a neighbourhood of
   0, so `iteratedDeriv j g 0 = iteratedDeriv (j − 1) (u ↦ DΨ(γ u)v) 0` (`Filter.EventuallyEq.iteratedDeriv_eq`).
3. Also `u ↦ DΨ(γ u)w` is constant on |u| < ε, so its first two derivatives vanish at 0:
   - `D²[v, w] + h′(0) D²[w, w] = 0`, hence h′(0) = 0, since `D²[v, w] = 0`;
   - `D³[v, v, w] + h″(0) D²[w, w] = 0` (using h′(0) = 0).
4. Differentiate `A(u) = DΨ(γ u)v` three times. The chain rule for `u ↦ D^nΨ(γ u)[m]` with fixed m is
   `D^{n+1}Ψ(γ u)[γ′(u), m]` (`iteratedFDeriv_succ_apply_left`; symmetry of the second and third derivatives of a
   C^∞ function, Mathlib `ContDiffAt.isSymmSndFDerivAt`, or the polarisation used in `CuspSanity`). At 0:
   - `A′(0) = D²[v, v] = 0`;
   - `A″(0) = D³[v, v, v] + h″(0)D²[w, v] = D³[v, v, v]`;
   - `A‴(0) = D⁴[v⁴] + 3h″(0)D³[w, v, v] + h‴(0)D²[w, v] = D⁴[v⁴] − 3D³[v, v, w]²/D²[w, w]`.

Fallback, if the general symmetry is costly: state and prove the lemma for `Ψ = triPhase α` only. There every mixed
derivative is an explicit trigonometric polynomial (generalise `triD2_mixed` and `triD3_mixed` to four slots), and
symmetry is `ring`. TRI-X needs only this case. The general form is the reusable one (K2), so it is preferred if it
costs at most about 1.5 times as much.

Use in TRI-X. `IsA5Point` gives v, w, ε, h with derivatives 1 to 5 of g zero. So `D³[v³] = 0` and `Qinv(v, w) = 0`,
since `D²[w, w] ≠ 0`.
- α ≠ 0: `TriAlgA5`.
- α = 0: v ≠ 0 in the kernel and `D²[w, w] ≠ 0` force exactly one of cos x, cos y to be zero. Say cos x = 0; then
  v = (v₁, 0) and `D³[v³] = v₁³ sin x ≠ 0`, a contradiction.

## 5. The A5 witness (part P-wit)

Fix |α| = a*, θ = arccos(−2α), so `cos θ = −2α`, `sin θ = √(1 − 4α²) = 1/√2`, and `4α² = 1/2`. Take the point
`k₀ = (θ, −θ)`, v = (1, 1), w = (1, −1), and any reduced curve h on |u| < ε. Then `γ(u) = (θ + u + h, −θ + u − h)`.
1. **Explicit forms, for every u:**
   - `triPhase α (γ u) = 2 cos u cos(θ + h) + α cos 2u`;
   - `DΨ(k₀)v = 0` and `DΨ(k₀)w = −2 sin θ`;
   - so `g(u) = 2 cos u cos(θ + h(u)) + α cos 2u + 2 sin θ · h(u)`.
2. **The reduced curve.** `DΨ(γ u)w = −2 cos u sin(θ + h)`, so ReducedCurve says `cos u · sin(θ + h(u)) = sin θ` on
   |u| < ε.
3. **The derivative of g.** On |u| < ε, `g′(u) = −2 sin u · δ(u)` with `δ(u) = cos(θ + h(u)) − cos θ cos u`. The
   h′ terms cancel by step 2.
4. **The δ-identity.** Squaring step 2 with `sin² = 1 − cos²`:
   `δ(u) · (2cos θ cos³u + δ(u) cos²u) = (2cos²θ − 1) sin²u − cos²θ sin⁴u = −(1/2) sin⁴u` on |u| < ε, since
   `cos²θ = 1/2`. This is a polynomial identity: `linear_combination`.
5. **Derivatives of δ.** δ(0) = 0 and `E(u) = 2cos θ cos³u + δ cos²u` has `E(0) = 2cos θ ≠ 0`. Leibniz at 0 on the
   identity of step 4, with the derivatives of `sin⁴` at 0 equal to (0, 0, 0, 0, 24), gives:
   - `δ^{(j)}(0) = 0` for j ≤ 3;
   - `δ⁽⁴⁾(0) = −12/(2cos θ) = 3/α`.
6. **Derivatives of g.** Leibniz on `g′ = −2 sin · δ`:
   - `g^{(j)}(0) = 0` for 1 ≤ j ≤ 5;
   - `g⁽⁶⁾(0) = 5 · (−2) · δ⁽⁴⁾(0) = −30/α = −60√2 · sign α`, since `1/α = 2√2 sign α` when |α| = a*.

   This proves TRI-W's third conjunct, for every reduced curve. Checked in SymPy for both signs.
7. **Existence of a reduced curve (TRI-W's first two conjuncts and TRI-K's A5 case).**
   - Let φ be a `ContDiffBump` at 0 with rIn = 1/8, rOut = 1/4, and ψ(u) = u φ(u). Then ψ is smooth, ψ = id on
     |u| < 1/8, and |ψ| ≤ 1/4 everywhere.
   - With `z(u) = sin θ / cos ψ(u)` we have `z ∈ (0, 1)`, since `cos(1/4) > 1/√2`.
   - Set `h(u) = π − θ − arcsin z(u)` if θ > π/2 (α > 0), and `h(u) = arcsin z(u) − θ` if θ < π/2 (α < 0).
   - h is C^∞ (`Real.contDiffAt_arcsin` off ±1), h(0) = 0, and step 2's equation holds on |u| < 1/8.
   - Then steps 1 to 6 give the derivatives, so `IsA5Point` holds at `(θ, −θ)`.
   - **Other points.** At `(−θ, θ)`, use w = (1, −1) and the curve −h: the swap `(x, y) ↦ (y, x)` maps the curve
     onto the first one. The same computation with θ replaced by −θ holds, since only cos(θ + h) and
     sin θ · h enter. At the shifted points `(±θ + 2πj₁, ∓θ + 2πj₂)` the same computation applies, by periodicity
     of cos and sin in the explicit forms. State the lemma for a general point with `cos x₀ = −2α`,
     `x₀ + y₀ ∈ 2πℤ` and `(sin x₀)² = 1/2`, and with `σ = sign(sin x₀)` in w.

Interfaces:
- `TriWitSextic α`: TRI-W's third conjunct.
- `TriWitA5 α k`: `|α| = a* → InLocus α k → IsA5Point (triPhase α) k`.

## 6. TRI-Q (part P-q)

Evaluation of the explicit forms of section 0. At (π/2, π/2): cos = 0, sin = 1, cos π = −1, sin π = 0, giving
`D²[w, w] = 4α`, `D⁴[v⁴] = 0`, `D³[v, v, w] = 2` and quartic −12. At (θ, −θ):
- `cos θ = −2α`, `sin²θ = 1 − 4α²`, and `cos 0 = 1`, `sin 0 = 0`;
- `D²[w, w] = 4α`, `D⁴[v⁴] = 12α` and `D³[v, v, w] = 2 sin θ`;
- so the quartic is `48α² − 12(1 − 4α²) = 12(8α² − 1)`.

## 7. Assembly

- **TRI-Q:** P-q.
- **TRI-W:** `TriWitA5` at `(θ, −θ)` and `(−θ, θ)` (both in `InLocus`, with j = 0), and `TriWitSextic`.
- **TRI-X:** P-bridge, then α = 0 (section 4) or `TriAlgA5`.
- **TRI-K:** `TriAlgClassify`, then `TriWitA5` in the third case.

## 8. Parts as planned for Lean

Each part is a proposition in a blueprint file, proved in its own file. No `sorry` anywhere; unfinished parts are
hypotheses of the assembly. Proof modules do not import sanity modules. The helper lemmas they need (`vec2_const`,
the polarisations, `triD*`) are re-proved or moved into a proof module, so that the closure of the final theorems
contains no sanity module, as in batch SPL.

| Part | File | Content | Size guess |
|---|---|---|---|
| P-deriv | OscInt/Front/TriDeriv.lean (planned) | Explicit forms of section 0, smoothness, half-angle rewriting | 150 lines |
| P-q | OscInt/Front/TriQuartic.lean (planned) | TRI-Q | 80 |
| P-EG | OscInt/Front/TriEG.lean (planned) | Section 3 | 120 |
| P-alg | OscInt/Front/TriAlg.lean (planned) | Section 2 (uses P-deriv, P-EG) | 400 |
| P-bridge | OscInt/Front/ReducedBridge.lean (planned) | Section 4, general Ψ (fallback: triPhase) | 300–500 |
| P-wit | OscInt/Front/TriWitness.lean (planned) | Section 5 | 400 |
| assembly | OscInt/Front/TriAssembly.lean (planned) | Section 7 | 100 |

Risks, said now:
- P-bridge: the symmetry of higher derivatives in Mathlib's API.
- P-wit: `iteratedDeriv` of products on a neighbourhood (`iteratedDeriv_mul` or a hand Leibniz). These two are the
  likely costs.
- P-alg: many cases, but each is algebra.

A route referee reads this document before the blueprint is written.
