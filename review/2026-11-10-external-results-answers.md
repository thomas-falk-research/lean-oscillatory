# Answers to the external reviewer's results of 2026-11-10

Subject: two results an external reviewer submitted on 2026-11-10, against branch
`claude/oscint-reviewer-handoff-9tn3je` at 89280d3: a hand proof and a counterexample, with scripts. The submission is
not recorded (owner privacy rule, lessons 46). The proof is re-derived below in the lead's words, in enough detail to
formalise from. Nothing was proved in Lean, and no frozen file changed.

## Verdict

Both results survive.

**Result 1 is the first result of its kind from this review process: a correct, complete pen-and-paper proof of a
frozen, unproved statement.**
- It proves S5.1′, the uniform cusp bound t^{−3/4} at any A3 point with C² amplitudes, uniform in the linear term.
  S5.1 follows, since a stable A3 point is an A3 point.
- The lead checked every step, and a fresh-context referee found no FATAL or MAJOR issue (summary below).
- It does not need the I3a lemma.
- It reuses proved OscInt infrastructure: the core estimate L6, `CoreEstimateFacts`, has exactly this structure for
  j ∈ {2, 3}, and S5.1 is its j = 4 case.

**Result 2 is a correct counterexample to an unfrozen strengthening.** It fixes I3a's input derivative budget.

Neither result is a new mathematical theorem in the literature sense; the reviewer claims none. The cusp exponent and
the dephasing mechanism are classical. C² amplitude control at a cusp, uniform in the linear term, was not found in
the reviewer's logged search: Ikromov–Müller and Borovyk–Goldberg state C³ norms (CITED-READ by the reviewer, not
re-read by the lead). The project-level value is large either way: the blocked theorem now has a complete,
constants-tracked route.

## Evidence the lead produced

- **Package integrity.** No member of the archive has an unsafe path. Its 362-file source snapshot is identical to the
  git objects at 89280d3 (0 differences).
- **The reviewer's five scripts,** read before running, run from the submission's own directory with `python3 -I`: all five
  pass. `check_cusp.py` asserts numpy 2.3.5, so it was run in a scratch virtual environment with the pinned packages;
  the other four ran under Python 3.13 with the session's packages. Maximum residual: 5.054e−16 here, against
  4.714e−16 reported.
- **Lead's checks:** `numerics/review/cusp_proof_checks.py`, 7/7, record
  `numerics/results-cusp-proof-checks-2026-11-10.txt`.
  - P1: the seven-term g⁗ chain rule, for an abstract F and h.
  - P2: h_u(0) = 0, h_uu(0) = −T/h₀, g⁗(0) = Q − 3T²/h₀, for a generic quartic jet.
  - P3: the identity for r″ and the polynomial U.
  - P4: 2η/λ + 36η^{−1/3} = 38λ^{−1/4}, and 38 = c₄ of S1.k.
  - P5: the non-stable coupled control F = u⁴ + (1+u)s²/2. Its reduced fourth derivative vanishes at (0, √2), which is
    why the proof splits at q₀.
  - Q1: the exact log(t/2) decomposition, for any cutoff S.
  - Q2, FLOAT: the counterexample's sampled Hessian budget is 42.21 at every t from 4 to 65536, consistent with uniform
    boundedness.
- **The lead's reading of the proof,** step by step against the frozen text:
  - `AmpBound` includes `ContDiff ℝ n A` (`StationaryPhase.lean:71`), so the Lean statement has no junk-value
    loophole.
  - VdC2 and VdC3 have constants 8/√μ and 18 μ^{−1/3}, with `ampNorm` = |ψ(b)| + ∫|ψ′|, as the proof uses.
  - M ≥ 0 follows from the order-0 bound.
  - The max-norm transport of the amplitude, ‖Le_i‖∞ ≤ ‖L‖, is correct.
  - The boundary terms vanish by continuity of A on ∂(closed ball) and on ∂R_δ.
  - No step uses T ≠ 0.
- **Fresh-context referee:** no FATAL or MAJOR finding; four NITs.
  - N1 matters for formalization: Mathlib's implicit function theorem gives smoothness *at* a point, so the proof's
    smoothness on a neighbourhood must be C⁴ on a neighbourhood, from finite-order `ContDiffAt` or from the IFT at every
    point plus uniqueness of the root.
  - N2–N4 are cosmetic.

## The proof of S5.1′, re-derived by the lead

**Setting.** φ ∈ C^∞(ℝ²) has `IsA3Point φ 0`, with witnesses v, w. Write h₀ = D²φ(0)[w,w] ≠ 0, T = D³φ(0)[v,v,w],
Q = D⁴φ(0)[v⁴] and Γ = Q − 3T²/h₀ ≠ 0. Then v ≠ 0 (else the invariant is 0), and v, w are independent (since
D²φ[v,·] = 0 while h₀ ≠ 0). Stability (T ≠ 0) is never used.

**Step 1: order-4 van der Corput from S1.3.** Let |f⁗| ≥ λ > 0 on [c,d], with f ∈ C⁴. Then f‴ is strictly monotone, so
{|f‴| < η} is an interval of length ≤ 2η/λ. On the at most two remaining intervals, S1.3 with amplitude 1 gives
18η^{−1/3} each. With η = λ^{3/4} the total is 38λ^{−1/4}, and the same holds on every [c,z]. Integrating by parts
against a C¹ amplitude B gives

  |∫_c^d e^{if} B| ≤ 38 λ^{−1/4} (|B(d)| + ∫_c^d |B′|).    (V4)

This is independent of S1.k, and 38 is c₄.

**Step 2: coordinates.** Put L(u,s) = uv + sw, J = |det L| and F(u,s) = φ(L(u,s)) − φ(0) − Dφ(0)[L(u,s)]. At 0:
F_u = F_s = F_uu = F_us = F_uuu = 0, F_ss = h₀, F_uus = T, F_uuuu = Q. The implicit function theorem for F_s(u,s) + q = 0
gives a curve s = c(u,q). It must be C⁴ on an open neighbourhood, which is the referee's N1: obtain it from
finite-order `ContDiffAt`, or apply the IFT pointwise and use uniqueness of the root. Put g(u,q) = F(u,c) + q·c. Then
g_u = F_u(u,c); the seven-term chain rule (check P1) and c_u(0) = 0, c_uu(0) = −T/h₀ (check P2) give g_uuuu(0,0) = Γ.

**Step 3: certificate (chosen from φ alone).** Put μ = |h₀|/2 and ν = |Γ|/2. Choose a, b > 0 with F_ss of fixed sign
and |F_ss| ≥ μ on R = [−a,a] × [−2b,2b]. Then shrink a and choose q₀ > 0 so that, for |u| ≤ a and |q| ≤ q₀, the curve c
is defined, |c| < b, and |g_uuuu| ≥ ν. Let D bound every partial derivative of F of order 2–4 on R. Put ρ = D/μ and
U = 1 + 7ρ/3 + 11ρ²/6 + ρ³/2. With α_u, α_s the ℓ¹ row norms of L⁻¹, choose
δ = min{a/(2α_u), b/(2α_s), q₀/(2D(α_u + α_s))}. For A with `AmpBound 2 (closedBall 0 δ) A M`, the amplitude a₀ = A∘L
has every partial derivative of order ≤ 2 bounded by N = max(1,‖L‖)²·M. Its support lies in
R_δ ⊂ [−a/2,a/2] × [−b/2,b/2], and |F_s| ≤ D(|u|+|s|) ≤ q₀/2 on R_δ.

**Step 4: the frozen integral.** It equals a unimodular constant times J ∫ e^{it(F + pu + qs)} a₀, where
p = Dφ(0)[v] + (y·v)/t and q = Dφ(0)[w] + (y·w)/t. Both p and q are arbitrary reals.

**Step 5: |q| ≤ q₀ (exact dephasing).** Put E = e^{it(F + qs − g)} and B(u) = ∫_{−2b}^{2b} E a₀ ds, so that the integral
is exactly ∫_{−a}^{a} e^{it(g + pu)} B(u) du. Then B′ = ∫ E {it[F_u(u,s) − F_u(u,c)] a₀ + (a₀)_u} ds.
- The Hadamard averages H = ∫₀¹ F_ss(u, c + θ(s−c)) dθ and K = ∫₀¹ F_us(…) dθ satisfy F_s + q = (s−c)H and
  F_u(u,s) − F_u(u,c) = (s−c)K, with |H| ≥ μ.
- So the t-term is r a₀ ∂_s E with r = K/H. One integration by parts (zero boundary terms) gives B′ = ∫ E W ds with
  W = (a₀)_u − ∂_s(r a₀).
- The bounds |r| ≤ ρ, |r′| ≤ (ρ + ρ²)/2 and |r″| ≤ ρ/3 + 5ρ²/6 + ρ³/2 (check P3) give |W_s| ≤ NU. Only amplitude
  derivatives of order ≤ 2 occur.
- S1.2 in s (second derivative ≥ tμ, W(u,2b) = 0) gives |B′| ≤ 32bNU(tμ)^{−1/2}. Since B(a) = 0, (V4) in u (fourth
  derivative ≥ tν) gives a bound of 2432·abU μ^{−1/2} ν^{−1/4} N t^{−3/4}.

**Step 6: |q| > q₀.** On R_δ, |F_s + q| > q₀/2, and a₀ vanishes on ∂R_δ. Integrating by parts once in s gives
(1/t) ∫_{R_δ} |∂_s(a₀/(F_s + q))| ≤ 4ab(2/q₀ + 4D/q₀²) N t^{−1}. The proof uses 4ab; ab suffices.

**Conclusion.** S5.1′ holds with δ as in Step 3 and
C = J·max(1,‖L‖)²·max{2432·abU μ^{−1/2} ν^{−1/4}, 4ab(2/q₀ + 4D/q₀²)}. δ and C are chosen from φ before A, M, y and t.
S5.1 follows, since `IsStableA3Point` implies `IsA3Point`.

**Referee findings (summary).** No FATAL or MAJOR finding. N1: the C⁴ neighbourhood, as in Step 2. N2: the area ab is
enough. N3: C ∈ ℝ suffices. N4: wording ("r is C² in s for fixed u, q"). The referee did not check the Lean-name
claims, the scripts, or the Mathlib-level measure details.

**Result 2, in brief.** For F(s) = |s|²/2 on ℝ² and t ≥ 4, take a radial amplitude
A_t(s) = t^{−2} e^{−it|s|²/2} w_t(|s|²)/|s|². Here w_t(q) = S(tq − 1)(1 − S(2q − 1)), with S a smooth step from 0 on
(−∞, 0] to 1 on [1, ∞). Then:
- A_t(0) = 0;
- the C² norm of A_t is bounded uniformly in t (the reviewer's bound is 16048 Euclidean; the lead's sampling gives 42.21,
  check Q2);
- ∫ e^{it|s|²/2} A_t = π t^{−2} log(t/2) exactly (check Q1).

So no remainder bound C‖A‖_{C²} t^{−2} can hold.

## Item by item

| Item | Bin | Disposition |
|---|---|---|
| Result 1: hand proof of S5.1′ (and S5.1) | **result** | Accept as the route for the A3 formalisation. `docs/proof-A3.md` should follow it. The lead's proposed parts are below; the route referee comes first, as CONTRIBUTING step 6 requires. Nothing is marked proved until the Lean proof is replayed. |
| Its claim that L6 core infrastructure exists for j = 2, 3 | already present (confirmed) | `Blueprint/StationaryPhase.lean`: `CoreHyps j` for any j, `CoreEstimateFacts` for j ∈ {2, 3} with rate m^{−(1/2+1/j)} and `AmpBound 2`; `Core.lean` has `amplitude_facts`, `ibp_phase`, `vdc2_wrap` and `hasDerivAt_reduced`. |
| Result 2: C²-only quadratic remainder fails in 2D | **result**, a precision fix | Added to ROADMAP I3a: a required bite datum, and the input budget must be fixed. |
| Result 2 part D: a parameter-norm remainder needs more than joint order 2 | correct (checked by reading, not re-derived) | Folded into the same I3a text. |
| S1.k | unchanged | Not needed for S5.1′, since V4 comes from S1.3. Still anticipated by Roos–Praveen, and still ported separately. |

## Consequences for the plan (owner decisions marked)

1. **A3 formalisation route** (to become `docs/proof-A3.md`, then a route referee, then proof parts):
   - P-V4: the order-4 van der Corput estimate from VdC3, as a smooth specialisation. It does not need S1.k.
   - P-core4: extend the L6 core estimate to j = 4, with the outer V4 replacing the S1.2/S1.3 outer step.
   - P-jet4: the reduced fourth derivative, its value Q − 3T²/h₀, and a C⁴ implicit curve on a neighbourhood (referee
     N1).
   - P-far: the large-q integration by parts.
   - Assembly: S5.1′, then S5.1 by weakening.

   Estimated difficulty: much lower than the I3a route, because the transverse machinery is already proved.
2. **Owner: I3 ordering.** I3a was put first on the premise that S5.1′ needed it, and that premise no longer holds.
   Recommendation: formalise A3 first by the route above, and keep I3a for the dimension track (I3b) and the leading
   terms. The dimension track still needs I3a.
3. **Disclosure (owner decision 2026-11-10).** Publishing practice (COPE, ICMJE) is to disclose AI assistance, naming the
   tool and version, and never to list an AI tool as an author or credit it. So the S5.1′ route is recorded as an
   AI-use disclosure in `docs/prior_art.md`: OpenAI ChatGPT 6, version as given by the owner. The eventual STATUS row
   and proof files will carry the same disclosure.
