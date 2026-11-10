# Answers to the external reviewer dossier of 2026-11-10

Subject: an external reviewer's dossier on `main` = 58a86d0, received by the owner on 2026-11-10. The dossier itself is
not recorded (owner privacy rule, lessons 46). Item labels (A1, C5, …) are the dossier's section labels. Each item is
stated below in the lead's words, before the finding. Written by the session-9 lead. Nothing was proved in Lean,
nothing frozen, and no statement or proof file was touched.

**Evidence.** `numerics/review/dossier_checks.py` was written from the dossier text alone, because its companion scripts
were not supplied. It has 27 checks: 18 exact SymPy checks (X1a–X1j, X2–X8, F6x) and 9 FLOAT TEST checks (F1–F3b, F4–F8).
The record is `numerics/results-dossier-checks-2026-11-10.txt`: OVERALL PASS 27/27. A FLOAT TEST covers only the sampled
case and is not an enclosure.

## Verdict in one paragraph

The dossier is careful, and its arithmetic holds up. Every formula I re-derived agrees, and every closed-form number
matches to the printed digits; sampled numbers agree where the dossier fully specifies the construction. It contains **no breakthrough for this project**, and its own closing summary says as much.

- What is genuinely new to the repository is small: closed forms of the QWZ cusp invariants **for every m > 2** (the
  repository had m = 3 exactly, and m = 2.05, 4 and 8 numerically).
- Its Lean questions 2–3 and its counterexample N2 are already answered by the frozen batch A3:
  - `OscInt/Front/CuspSanity.lean` has the bite `(y + x²/2)²`;
  - `docs/statements.md` shows the existential form is equivalent to the universal one, which forces v ≠ 0;
  - the `∀ y` quantifier in S5.1 covers a nonzero gradient.
- Parts C (analytic-symbol locality, aliasing, error budgets) and D (Combes–Thomas-type weighted bounds on graphs) are
  correct but classical, and mostly outside OscInt's subject, which is oscillatory-integral decay. Whether any of them
  enters the programme is an owner scope decision.
- I found two minor derivation defects (C5.3, C6.1) and two completeness points (the four cusp points; underspecified
  seeded chains), listed at the end. None changes a conclusion.

## Item by item

| Dossier item | Lead's finding | Evidence |
|---|---|---|
| A1 cusp witness, all m > 2 | **Confirmed.** P(a,a) = D/m². ω_su = ω_uu = ω_uuu = 0. ω_ss, ω_suu, ω_uuuu and Γ_m are as stated, and p(z) > 0 for z > 4, so Γ_m < 0 and ω_suu ≠ 0. On the diagonal, ω_uu = 0 iff cos b = −1/m, so the diagonal holds no other rank-one point. The m = 3 values match CENSUS spec §7 / K-QWZ3. | X1a–X1j (exact) |
| A1, the four points | **Clarification (NOTE).** The dossier names one point and one ray. The A3 points are the four points (±a, ±a), and the upper-band signed rays are x/t = ∇ω, i.e. (∓v_m, ∓v_m) with signs opposite to the point's (by evenness of ω in each variable). The census expectation K-QWZ3 already lists four points. | X1i, X1j |
| A1, normalisation | **Clarification.** Lean `IsA3Point` tests H[w,w]·Q − 3T², while CENSUS spec §2.2 defines g4 = Q − 3T²/H[w,w], which is the dossier's Γ. Their nonvanishing and sign agree. The numbers differ by the factor ω_ss: at m = 3 the Lean quantity is −55968/4225 ≈ −13.247 and Γ = −5247/√65. Anyone comparing values across the two must rescale. | X1f–X1h |
| A1.6 local constant ~ m^{5/4} | Not checked. It is a formal leading-term scaling, which the dossier labels as such; it has no theorem behind it. | — |
| A2 reduced fourth jet | **Confirmed** for r = 2 with fully symbolic H, v, Q and the higher jet terms that could interfere (s²u, s u³, s³). The general-r statement is standard (splitting lemma) and was not re-derived for all r. | X2 |
| N2 counterexample | **Confirmed, and already in the repository.** It is `(s + u²/2)²/2`, which is half of the frozen bite `(y + x²/2)²` in `OscInt/Front/CuspSanity.lean`. | X3 |
| Lean Q2 (v ≠ 0 forced; w choice) | **Confirmed, and already documented** (`docs/statements.md`, batch A3). With v = 0 the invariant is 0. Replacing w by w + cv leaves it unchanged when Hv = 0 and T[v,v,v] = 0. | X4 |
| Lean Q3 (no ∇φ = 0 in IsA3Point) | Intended. S5.1 quantifies over every linear term y, which absorbs the gradient (`docs/statements.md`, batch A3). | reading |
| A3 uniformity in y | The dossier's flag matches what both pre-proof referees already raised (`review/2026-11-09-A3-pre-proof-{A,B}.md`). The missing tool is the parametrised 1D stationary-phase lemma (`docs/HANDOFF.md`, "Next"). Nothing new. | reading |
| B1 Gaussian lift, B2 Schur shear | Confirmed: B2 exactly on the R18 data; B1 is classical. Neither yields a non-separable higher-dimensional theorem, as the dossier itself says (N9). | X8 |
| C1 LE vs Landau | **Confirmed.** (A+B)² = 4754.047960596477752, c = 0.7857468704985129, and the ratio is 195.04665. N7: `docs/prior_art.md` already gives c = 0.785746870498513… and calls 0.7857 "correct to four places", which is true as a truncation. The dossier's caution is right: 0.7857 < c, so 0.7857 must never be used as an upper bound. No repository text uses it as one; the registered LE threshold was 0.7858 + 1e−4, above c. On ν = 0: c is attained at ν = 0 (`docs/prior_art.md` quotes the EJDE paper, ν ≥ 0), so the dossier's "positive ν" worry about the JLMS abstract does not affect the repository's citation. | F8 |
| C2 velocity ≤ 1, signed ray | **Confirmed**, including 0 < v_m < 1. The identity holds for every real m wherever ω > 0. | X5, X1j |
| C3 separable reference | **Confirmed.** Projector algebra is exact; the bound is never exceeded on 400 random momenta at six (m, t). | X7, F1 |
| C4 corrected reference | **Confirmed numerically**; the sampled maxima match R12's within sampling. The van der Corput constants A_m, B_m (C4.5) are plausible but unchecked: the LE partition's other hypotheses were not re-read for f_m. | F1 |
| C5 analytic-symbol locality | **Conclusion confirmed; the stated reason is MINOR-defective.** Step 3 bounds Im H_m(k+iθ) term by term, using only that each Pauli matrix has norm one, which gives 2(sinh θ₁ + sinh θ₂), not sinh θ₁ + sinh θ₂. The claimed B(η) = sinh η₁ + sinh η₂ holds by the exact identity ‖b·σ‖ = \|b\| for real b, with \|b\|² = sh₁² + sh₂² + 2 sin k₁ sin k₂ sh₁ sh₂ ≤ (sh₁ + sh₂)². The bound is mass-free; it is checked at m = 2 (gapless) as well as m = 3, with max ratio 0.20 against the optimised bound. The result is classical: Combes–Thomas, and Bessel-type bounds for the free lattice propagator. | X6, F2 |
| C6 aliasing | **Bound confirmed** (8.4751320538e−9; observed 2.4368e−13 against the dossier's 2.4317e−13, the difference coming from the reference grid). **MINOR ambiguity in the identity:** on the grid k_j = −π + 2πj/N with N odd, the alias sum carries signs (−1)^{N(ℓ₁+ℓ₂)}. The unsigned form holds on the grid starting at 0. The norm bound is unaffected, since it uses the triangle inequality. A test that tells the two forms apart needs aliases of order one. At N = 5, t = 3, x = (−1, 0), the signed sum matches K_5 to 1.2e−15 and the unsigned sum misses it by 0.12. At N = 65 the aliases are below 1e−9, so no test there can discriminate (a first version of F3b passed for that reason and was replaced). | F3, F3b |
| C7 parameter budget | Elementary (Duhamel); not re-run. | — |
| D1 / D3 weighted locality, weak link | **Confirmed.** η, β, both bounds, the row-sum invariant, and the sampled amplitude 5.6809e−7 all reproduce. | F4 |
| D4 truncation | Inequality confirmed on an own instance. The dossier's exact draw is not fully specified (onsite law assumed U(−0.7, 0.7)). Got error 4.34e−5 against bound 2.57e−4; the dossier reported 4.42e−5 and 2.75e−4. | F5 |
| D5 Riesz projector | **Premise proved exactly:** for m = 1, P − 1 = 2(1 + cos k₁)(1 + cos k₂) ≥ 0, so the band is ⊂ [1, 3] and δ = 1/2 holds. The strip estimate ‖H(k+iθ) − H(k)‖ ≤ 4 sinh(0.05) holds because \|sin(k+iθ) − sin k\| ≤ sinh θ (and the same for cos). Classical. | F6, F6x |
| D2 / N10 Kerr | Confirmed: ratio 199.8686933. The dossier's own conclusion is correct: no g-independent nonlinear stability. | F7 |
| E1–E6 | Not checked. These are roadmap items with no derivation to check. | — |
| R20 CI status | **Resolved.** `ci` run 42715917621 and `verify` run 42715918012 on 58a86d0 both completed **success**. So the 52 proved and the 3 stated-not-proved (S1.k, S5.1, S5.1′) stand as in `docs/STATUS.md`. | GitHub Actions API, 2026-11-10 |

## What the project could take from it (recommendations; owner decides)

1. **Adopt A1 as an exact control (low cost, in scope).**
   - **For CENSUS.** M08 (QWZ m = 3) becomes one member of a parametric family with a closed-form A3 locus. The
     implementations must find it, and must agree with Γ_m and v_m, at several rational m. This is a cheap,
     discriminating cross-check, and it is already consistent with K-QWZ3.
   - **For non-vacuity.** ω_m is smooth on all of ℝ² (P ≥ (m − 2)² > 0). So φ(κ) = ω_m(k₀ + κ) − ∇ω_m(k₀)·κ is a
     real-model datum with `IsStableA3Point φ 0`, using v = (1, −1) and w = (1, 1).
   - Proving that in Lean needs iterated derivatives of √∘trig at an algebraic point. That is a sizeable side project,
     worth it only once S5.1 is proved and a model consumer is wanted.
2. **Do not reopen QWZ as the VV acceptance model** on the strength of A1. A1 confirms the erratum
   (`docs/design/vector-amplitudes.md` §6): QWZ for m > 2 needs a proved S5.1 plus a global assembly with A3 points
   (HANDOFF "Next" (4)).
3. **C5 + C6 (analytic-symbol exponential locality, alias bound): a scope decision.** They are elementary given Mathlib's
   complex analysis, they need no band diagonalisation or gap, and they would give the industry programme a usable
   finite-grid certificate. But they are classical and not oscillatory-integral decay. If adopted, it should be as a
   separate batch under the full statement-first protocol. No prior-art sweep has been run for a formalisation.
4. **D1–D5: outside OscInt's core**, as the dossier itself suggests (an optional package). They are classical
   Combes–Thomas-type results.
5. **Process.** An external review does not satisfy CONTRIBUTING step 5 for batch A3. It was not blind, and it does
   not judge a frozen statement against its prose as its subject.

## Corrigendum: defects in the dossier (none refutes a final bound)

- C5.3: the term-by-term norm argument proves only 2(sinh η₁ + sinh η₂). Replace it with ‖b·σ‖ = \|b\| and the identity in X6.
- C6.1: state which grid the sampled Fourier coefficient uses. On k_j = −π + 2πj/N with N odd, the alias identity has signs
  (−1)^{Nℓ}.
- A1 / C2.4: list the four A3 points and their four signed rays, not one.
- D4.4 and D3.3: give the full construction of the seeded chains (onsite law, which edge is weak, ordering), so the
  sampled numbers can be reproduced; the closed-form bounds reproduce already.
- Scope of "new": the N2 counterexample (`OscInt/Front/CuspSanity.lean`, bite `(y + x²/2)²`), Lean questions 2–3
  (`docs/statements.md`, batch A3) and the m = 3 values (CENSUS spec §7) were already in the repository. New at project
  level: the closed-form QWZ cusp invariants for every m > 2.

## Follow-up round (2026-11-10)

The reviewer accepted the findings above and recommended two things: the all-m QWZ CENSUS control, and a scoped C5/C6
proof-of-value outside the core. The owner adopted both (CENSUS spec K-QWZm; ROADMAP I7). One further observation,
**CHECKED BY HAND, classical**: for a translation-invariant lattice operator with kernel `h(x − y)` and symbol
`Ĥ(k) = Σ_n h(n) e^{−ink}`, conjugation by `e^{η·x}` gives kernel `h(n) e^{η·n}`, that is, symbol `Ĥ(k + iη)`. So C5's
complex shift and D1's weight conjugation are one mechanism, the Combes–Thomas one.
