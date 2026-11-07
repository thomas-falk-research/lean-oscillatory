<!-- Blind statement review of front-end batch 1 (F1, F2), referee A (fresh-context agent, prompt review/prompts/API1-pre-proof.md), commit eb8e621. Verbatim final report. -->

eb8e6214e96dcf4ca24cfad2cff15f12ed962336

(I got the hash by reading `.git/HEAD` and the ref file directly, because my launch instructions said no git operations. I read only the files the prompt lists. Scratch files are in /tmp/apiA/ and nothing in the repository was touched.)

# Referee A report: F1 `AmpBoundOfContDiffStatement`, F2 `D4LimitClosedFormStatement`

**Summary: both statements are FAITHFUL to `docs/statements.md` and both are TRUE, F2 assuming S4.2 and S4.4. I found no BLOCKER or MAJOR issues, only two MINOR points and a few NITs.**

## 1. Verdicts

**F1: FAITHFUL, TRUE.** The Lean text `∀ n K A, IsCompact K → ContDiff ℝ n A → tsupport A ⊆ K → ∃ M, AmpBound n K A M` matches the docs exactly. Both `ContDiff ℝ n` occurrences, in F1 and inside `AmpBound`, use the same cast of `n : ℕ`. I proved it in /tmp/apiA/Bridge.lean as `F1_true`; the axioms are only `propext, Classical.choice, Quot.sound`. The proof:
- `tsupport A ⊆ K` with K compact gives `HasCompactSupport A`.
- For each j ≤ n, `continuous_iteratedFDeriv` and `bddAbove_range_of_hasCompactSupport` give a bound.
- M is the sum of `max B_j 0` over j ≤ n.

**F2: FAITHFUL to the docs' F2, TRUE given S4.2 and S4.4.**
- **Does it say the brief's S4?** Yes. For Disc C < 0 the limit is `t^{2/3} ∫ e^{itφ} A → Γ(1/3)²/(√3|Disc|^{1/6}) · A(0)`, and the `if D < 0` branch of `d4ClosedConstant` is that constant. F2 also covers Disc > 0 (the elliptic umbilic). That goes beyond the brief, which only mentions negative discriminant, but it matches the docs.
- **Elliptic branch is right.** I computed c_C = I·J(C)/3 with mpmath (30 digits; `/tmp/apiA/num.py`) and compared it with `d4ClosedConstant (disc q)`:

| q = (a, b, c, d) | Disc | ratio to closed form |
|---|---|---|
| (1, 2, 3, 5) | −367 | 1 − 2e−11 |
| (2, −7, 3, 1) | 733 | 1 − 1e−11 |
| (1, −1, −2, 1) | 49 | 1 − 2e−11 |
| (3, 1, −4, −2) | 252 | 1 − 2e−11 |
| (1, 0, 0, 1) | −27 | 1 − 8e−12 |
| (1, 0, −3, 0) | 108 | 1 + 4e−14 |
| (0, 1, 1, 0) | 1 | 1 − 3e−11 |

   The first four rows are cubics with all coefficients nonzero, of both signs.
- **Independent checks:**
  - I = Γ(2/3)/2 = 0.6770589697 (quadrature on [0, 1] plus `quadosc` on [1, ∞)). Note that `quadosc` on [0, ∞) in one piece wrongly gives 0.67628, because of the singularity at 0.
  - By hand, ∫ e^{i(x³+y³)} = (Γ(1/3)/√3)² = Γ(1/3)²/3, which agrees with `sanity_d4ClosedConstant_cubes`.
  - The formula transforms correctly: scaling C → λC multiplies J by |λ|^{−2/3} and Disc by λ⁴. A linear change of variables with determinant det g multiplies Disc by (det g)⁶ and the integral by |det g|^{−1}.
- **Truth of the limit itself:** this is S4.2's responsibility. It is classical, and C² amplitudes reduce to smooth ones by approximation in the C² norm together with the uniform bound S4.1′.

## 2. Is F2 implied by S4.2, S4.4 and F1?

Yes, confirmed by Lean. `F2_of (h2 : D4LimitStatement) (h4 : D4ConstantClosedFormStatement) (hF1 : AmpBoundOfContDiffStatement) : D4LimitClosedFormStatement` compiles in /tmp/apiA/Bridge.lean (about 10 lines; axioms `propext, Classical.choice, Quot.sound`). S4.3 is not needed. The steps:
- F1 with K = `closedBall 0 δ` gives an M; `exact_mod_cast` handles `ContDiff ℝ 2` versus `ContDiff ℝ ↑(2:ℕ)`.
- Split on the sign of Disc ≠ 0 and rewrite `d4Constant` to `d4ClosedConstant` using `h4.2.1` / `h4.2.2` and `if_pos` / `if_neg`.
- Apply S4.2's limit.

F2 is strictly a front end; nothing stronger slipped in:
- **Order of quantifiers:** `∃ δ > 0` comes before `∀ A`, as in S4.2, and δ depends only on φ.
- **Integral:** the written-out integral is definitionally `oscInt2 (fun κ => t * φ κ) A`; I checked this by `rfl`. Same measure (volume on ℝ×ℝ), same `↑(t * φ k) * Complex.I`.
- **Coercions:** `((t ^ ((2:ℝ)/3) : ℝ) : ℂ)` is identical to S4.2's.
- **Support:** both use `tsupport`, which is what `AmpBound` uses.
- **Ball:** both use `Metric.closedBall 0 δ` in the max norm.
- **Phase hypotheses:** they are copied verbatim from S4.2.
- **What is lost:** dropping M only loses uniformity, which a limit statement does not use.

## 3. Vacuity and conventions

- **`d4ClosedConstant 0` and its `if`:** at D = 0 it equals `Γ²/0^{1/6} = Γ²/0 = 0` (checked by `simp`). This is junk, but it is unreachable because F2 assumes `disc ≠ 0`.
- **`Real.rpow` of `|D|` and of `D`:** the negative branch takes `|D|`, so `Real.rpow` of a negative number never occurs. The `else` branch takes `D ^ (1/6)` and is only reached with D ≥ 0.
- **F1 is not trivially false for any n:**
  - n = 0: it says a continuous function with compact support is bounded, since `iteratedFDeriv ℝ 0 A k` has the norm of `A k`.
  - Orders above n: these are never constrained, because `AmpBound` asks only j ≤ n.
  - K empty: this forces A = 0, so M = 0 works.
  - Compactness of K is genuinely needed: without it, a constant A is a counterexample.
- **F1 is easy, but not tautological.**
- **F2 is not vacuous:**
  - `sanity_D4Limit_hyps` shows the hypotheses are satisfiable (x³+y³).
  - For any δ there is a bump with A(0) = 1 (`sanity_ampBound_exists`).
  - The constant is positive whenever D ≠ 0 (`sanity_d4ClosedConstant_pos`).
  - So the conclusion forces `t^{2/3} |∫ e^{itφ} A| → c > 0`.

## 4. Sanity theorems in `FrontEnd.lean`

I could not see "lessons 11, 17", because they are outside my reading list. I judged the sanity theorems against the general rule: test through the same definitions, and show bite.
- **`sanity_AmpBoundOfContDiff_hyps`**
  - What it checks: F1's hypotheses, using F1's own predicates (`ContDiff`, `tsupport`, `IsCompact`), for one bump, at n = 2 only.
  - What it misses: it does not test the conclusion. That is acceptable, since M is existential and `sanity_ampBound_exists` already shows `AmpBound` is satisfiable with A(0) = 1.
- **`sanity_d4ClosedConstant_cubes`**
  - What it checks: it is correct (`d4ClosedConstant (-27) = Γ(1/3)²/3`), and it agrees with the textbook value I verified by hand.
- **`sanity_d4ClosedConstant_branches`**
  - The docstring arithmetic is right: x³+2x²y+3xy²+5y³ gives 36−108−160−675+540 = −367, and xy(x+y) gives 1.
  - It detects writing `D` instead of `|D|` in the negative branch: `Real.rpow (-367) (1/6)` is not 367^{1/6}, so `norm_num` would fail.
  - It detects swapping the branches, through the √3 factor at D = 1.
  - It cannot detect `|D|` instead of `D` in the positive branch, but that change is harmless.
  - What it misses: these are pure unfoldings, so they check `d4ClosedConstant` only against its own formula. An error shared by `d4ClosedConstant` and S4.4 (for example a wrong exponent in both) would pass all of them. That is covered only by numerics: mine, and `numerics/results-d4const-2026-11-06.txt`, which I did not read.
  - No sanity theorem exhibits an elliptic (Disc > 0) phase satisfying F2's hypotheses, and none uses a phase whose cubic part has all coefficients nonzero.
- **`sanity_d4ClosedConstant_pos`**
  - What it checks: correct and useful bite (no junk 0 when D ≠ 0).

## 5. Findings

No BLOCKER. No MAJOR.

**MINOR**
1. The text `theorem sanity_d4ClosedConstant_branches : d4ClosedConstant (-367) = … ∧ d4ClosedConstant 1 = Real.Gamma (1 / 3) ^ 2` only re-derives the definition. Nothing in Lean ties `d4ClosedConstant` to the Gamma-free `d4Constant`; that link is S4.4, unproved, and supported only by numerics. My numerics agree to about 1e−11 on seven cubics, four of them with all coefficients nonzero. The docstring's claim "a swap … would show here" is true only for literal swaps in the definition.
2. No F2-level sanity theorem exhibits an elliptic phase satisfying the hypotheses (for example x³ − 3xy², Disc = 108 > 0). `sanity_D4Limit_hyps` covers only x³+y³ (Disc < 0), so the `disc > 0` half of F2 has no exhibited instance.

**NIT**
1. In `d4ClosedConstant`, the `else` branch also catches D = 0, where it returns the junk value 0. The docstring says "used for `D > 0`"; it would be clearer to state the D = 0 value explicitly.
2. `sanity_AmpBoundOfContDiff_hyps` fixes n = 2, while F1 is stated for all n. Using a general `(n : ℕ)` would cost nothing; `ContDiffBump` is C^∞.
3. The F2 text in the docs says "This is S4.2 ∧ S4.4 with F1". It is, but S4.4's first conjunct (`cosMoment = Γ(2/3)/2`) and S4.3 are not used; only S4.4's two `disc`-sign conjuncts are.

Files: `/tmp/apiA/Bridge.lean` (F1 proof, F2 bridge, convention checks; compiles cleanly) and `/tmp/apiA/num.py` (the numerics).
