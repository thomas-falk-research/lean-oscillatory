# Proof route for batch HW (HW-R, HW-K, HW-D, HW-L)

Written by the lead on paper before the freeze of the batch (the file in the lead's scratch was last written at
2026-11-16T21:43:36Z; its outline is the paragraph "Route" of `docs/statements.md`, Batch HW, which was frozen with the
statements at 22:58:03Z); kept outside the
repository until the review answers were stamped (`stamps/20261117T010311Z-a93c4e1e44f7`, 2026-11-17 01:03:18Z;
rule 1). The mathematics is known (`docs/prior_art.md`, batch HW). Status of this page: a route on paper, to be read
by a route referee before the parts are proved; not a proof record.

Notation as in `docs/statements.md`, "Batch HW": step U, kernel K(t, x), ω(k) = arcsin(sin k/√2),
g(k) = 1/√(2(1 + cos² k)), so that the integrand of K is g(k)(e^{−itω(k)} − (−1)^t e^{itω(k)}) e^{−ixk}.

## H1. Pointwise identities (data of the dispersion relation)
sin ω = sin k/√2; cos ω = √(1 − sin² k/2) > 0 (|ω| ≤ π/4); 2 cos ω = √(2(1 + cos² k)) = 1/g.
With λ₊ = e^{−iω}, λ₋ = −e^{iω}: λ₊ + λ₋ = −2i sin ω = −i√2 sin k =: τ(k), λ₊λ₋ = −1, so λ² = τλ + 1 for both.
α_t := g (λ₊^t − λ₋^t). Then α_0 = 0, α_1 = g(λ₊ − λ₋) = 2g cos ω = 1, α_{t+2} = τ α_{t+1} + α_t.

## H2. The kernel recursion (part `HadamardKernelRecFacts`)
K(t, x) = (2π)^{−1} ∫_{−π}^{π} α_t(k) e^{−ixk} dk. Hence K(0, x) = 0; K(1, x) = (2π)^{−1} ∫ e^{−ixk} dk = [x = 0];
and since τ(k) e^{−ixk} = (e^{−i(x+1)k} − e^{−i(x−1)k})/√2 (as −i√2 sin k = (e^{−ik} − e^{ik})/√2),
K(t + 2, x) = (K(t + 1, x + 1) − K(t + 1, x − 1))/√2 + K(t, x). (Linearity of the interval integral; all integrands
are continuous.)

## H3. HW-R (assembly)
W_t(x) := ((a + b)/√2 · K(t + 1, x + 1) + a K(t, x), (a − b)/√2 · K(t + 1, x − 1) + b K(t, x)).
W_0 = U δ_{a,b} by K(1, ·), K(0, ·) and the definition of the step. U W_t = W_{t+1} by the recursion H2 (first
component: (W_t(x+1)₁ + W_t(x+1)₂)/√2 = (a+b)/2 · K(t+1, x+2) + (a−b)/2 · K(t+1, x) + (a+b)/√2 · K(t, x+1), and the
recursion at (t, x + 1) turns (a+b)/√2 · K(t+2, x+1) + a K(t+1, x) into the same expression; second component
alike). Induction on t with U^{t+1} = U ∘ U^t.

## H4. The phase (part `HadamardPhaseFacts`)
On ℝ: ω′ = cos k (1 + cos² k)^{−1/2}, ω″ = −sin k (1 + cos² k)^{−3/2}, ω‴ = −cos k (4 − 2cos² k)(1 + cos² k)^{−5/2}
(arcsin is differentiable at sin k/√2 because |sin k/√2| < 1). Lower bounds:
|sin k| ≥ 1/√2 ⟹ cos² k ≤ 1/2 ⟹ |ω″| ≥ (1/√2)(3/2)^{−3/2} = 2/(3√3).
|cos k| ≥ 1/√2 ⟹ |ω‴| ≥ 2^{−3/2}: with c = |cos k| ∈ [1/√2, 1], c(4 − 2c²) ≥ 2^{−3/2}(1 + c²)^{5/2}; at c = 1 equality.
Proof of the last: (1 + c²)^{5/2} ≤ 2^{3/2}(1 + c²) for c² ≤ 1, so it is enough that c(4 − 2c²) ≥ 1 + c², i.e.
p(c) = −2c³ − c² + 4c − 1 ≥ 0 on [1/√2, 1]: p(1) = 0 and p(c) = (1 − c)(2c² + 3c − 1), with 2c² + 3c − 1 > 0 for c ≥ 1/2.

## H5. The amplitude (part `HadamardAmplitudeFacts`)
g′ = sin k cos k/(√2 (1 + cos² k)^{3/2}); g is continuous, g′ continuous (integrable). On an arc [jπ/2 − π/4,
jπ/2 + π/4] the sign of g′ changes once, at the midpoint, so ∫|g′| is the sum of the two one-sided variations:
cos-arcs (j even): g(end) = 1/√3, g(mid) = 1/2, ampNorm = 1/√3 + 2(1/√3 − 1/2) = √3 − 1;
sin-arcs (j odd): g(end) = 1/√3, g(mid) = 1/√2, ampNorm = 1/√3 + 2(1/√2 − 1/√3) = √2 − 1/√3.
(An upper bound for ampNorm is enough.)

## H6. HW-K (part `HadamardKernelBoundFacts`, from H4, H5 and S1.k as proved in the library)
For σ = ±1 let I_σ(t, x) = ∫_{−π}^{π} g(k) e^{i(σtω(k) − xk)} dk, so K = (2π)^{−1}(I_{−1} − (−1)^t I_{+1}) and
|K| ≤ (|I_{−1}| + |I_{+1}|)/(2π). The integrand is 2π-periodic (x ∈ ℤ), so the integral over [−π, π] equals the
integral over [−π/4, 7π/4], the union of the arcs [−π/4, π/4], [π/4, 3π/4], [3π/4, 5π/4], [5π/4, 7π/4].
On a sin-arc: S1.k, k = 2, chain (σtω, σtω′, σtω″), μ = 2t/(3√3), linear term p = −x:
|∫| ≤ 8 (2t/(3√3))^{−1/2} (√2 − 1/√3). On a cos-arc: k = 3, μ = 2^{−3/2} t: |∫| ≤ 18 (2^{−3/2} t)^{−1/3} (√3 − 1).
Sum: |K| ≤ (2/(2π)) [2 · 8 · (3√3/2)^{1/2} (√2 − 1/√3) t^{−1/2} + 2 · 18 · √2 (√3 − 1) t^{−1/3}]
= 6.8699… t^{−1/2} + 11.8633… t^{−1/3} ≤ 7 t^{−1/2} + 12 t^{−1/3}.
(The two numerical inequalities (16/π)(3√3/2)^{1/2}(√2 − 1/√3) ≤ 7 and (36/π)√2(√3 − 1) ≤ 12 are to be proved from
rational bounds on √2, √3, π.)

## H7. HW-D (assembly or a part)
t = 1: U δ_{a,b} has components (a + b)/√2 at −1 and (a − b)/√2 at +1; ≤ (|a| + |b|)/√2 ≤ 39 (|a| + |b|).
t ≥ 2: by HW-R with t − 1 ≥ 1 and HW-K at t and t − 1:
|first component| ≤ (|a| + |b|)/√2 · (7 t^{−1/2} + 12 t^{−1/3}) + |a| (7 (t−1)^{−1/2} + 12 (t−1)^{−1/3}),
and t^{−1/2} ≤ t^{−1/3}, (t − 1)^{−1/2} ≤ √2 t^{−1/2} ≤ √2 t^{−1/3}, (t − 1)^{−1/3} ≤ 2^{1/3} t^{−1/3} (t − 1 ≥ t/2):
≤ (|a| + |b|) t^{−1/3} (19/√2 + 7√2 + 12 · 2^{1/3}) and 19/√2 + 7√2 + 12 · 2^{1/3} = 38.4535… ≤ 39.

## H8. HW-L (part `HadamardLinearityFacts` plus assembly)
The step is additive, commutes with multiplication by a scalar and with translations of the lattice; so does U^t. A
state of finite support S is the finite sum over y ∈ S of the translate by y of δ_{ψ₀(y)}; apply HW-D to each term:
|component| ≤ Σ_{y∈S} 39 (|ψ₀(y)₁| + |ψ₀(y)₂|) t^{−1/3}, and the finite sum over S is the `finsum` of the statement.

## Blueprint and assembly (written after the review answers were stamped)
`Blueprint/HadamardWalk.lean`: definitions `hwD1`, `hwD2`, `hwD3` (ω′, ω″, ω‴ with (1 + cos² k)^{3/2} written as
(1 + cos² k)·√(1 + cos² k)), `hwAmp`, `hwAmp'` (g and g′ as complex-valued functions); propositions
`HadamardKernelRecFacts` (H2), `HadamardPhaseFacts` (H4), `HadamardAmplitudeFacts` (H5), `HadamardDecayArithFacts`
(the arithmetic of H7 for t ≥ 2, stated at the times t + 1 and t), `HadamardLinearFacts` (H8: the walk from a state
supported in a finite set S is the sum over S of the translated walks from point states).
Assembly by the lead, `OscInt/Front/HadamardWalkAssembly.lean`, compiled before any part
(`hadamardKernelFormula_of`, `hw_component_le`, `hadamardDecay_of`, `hadamardDispersive_of`): HW-R from H2 by
induction (H3); HW-D from HW-R, HW-K, K(0, ·) = 0 and the arithmetic fact (t = 1 directly: 19/√2 ≤ 39); HW-L from
HW-D and H8. HW-K is a part: from H4, H5 and the proved S1.2 (`OscInt.vanDerCorput_two`) and S1.3
(`OscInt.vanDerCorput_three`), as in H6.

Parts (one agent each, one Lean file each):
| Part | Proves | Uses |
|---|---|---|
| HW1 | `HadamardKernelRecFacts` | H1, H2: integrals of explicit integrands over [−π, π] |
| HW2 | `HadamardPhaseFacts`, `HadamardAmplitudeFacts` | H4, H5: derivatives of arcsin(sin k/√2) and of g; exact variation of g on four arcs |
| HW3 | `HadamardKernelBoundStatement` from `HadamardPhaseFacts` and `HadamardAmplitudeFacts` (as hypotheses) | H6: periodicity, four arcs, S1.2 and S1.3, the two numerical inequalities |
| HW4 | `HadamardDecayArithFacts`, `HadamardLinearFacts` | H7 (real powers), H8 (induction on the time) |

## Interface checks (numerical, run before the route referee)
`numerics/review/hw_interface_checks.py`, results `numerics/results-hw-interface-checks-2026-11-17.txt`: 8 lines, all
pass (the derivative chain and the amplitude derivative by numerical differentiation; the two lower bounds on a grid
of a period; the four amplitude norms, which equal their stated bounds; the arithmetic fact for t up to 10^15,
largest ratio of its two sides 0.944 at t = 1; the kernel recursion; the linear decomposition on random states).

## Risks
- H5: the bounds for the amplitude norm are equalities, so the integral of |g′| must be evaluated exactly on each
  arc (g′ changes sign once, at the midpoint).
- H4: the two lower bounds are attained (at sin k = ±1/√2 and at cos k = ±1).
- H6: moving the window of integration by periodicity; matching the shape `oscInt (fun x => φ x + p * x) ψ a b` of S1
  with the kernel's integrand (the linear term is −x·k; the amplitude is g; the phase is ±t ω).

## Revision after the route referee (2026-11-17)

The route referee read the route as committed in bcad78c (verdict: sound; no BLOCKER, no MAJOR; three MINOR, five
NIT; `review/2026-11-17-HW-route-answers.md`). In this batch the parts were launched together with the referee, not
after it; no finding required a part to be redone. The text above is the reviewed text and is left as it was; these
items override it.
1. Names. The headings of H6 and H8 name parts `HadamardKernelBoundFacts` and `HadamardLinearityFacts`; neither
   exists. HW-K is proved as the frozen statement itself (from `HadamardPhaseFacts` and `HadamardAmplitudeFacts`), and
   the linearity proposition is `HadamardLinearFacts`. The blueprint has five propositions, not six (its header said
   six and is corrected).
2. Obligations of the part HW3 that neither of its hypotheses supplies: interval integrability of `hwAmp'` (from its
   continuity) and the facts |sin k| ≥ 1/√2 and |cos k| ≥ 1/√2 on the four open arcs. The part proves them.
3. Slack: none in the four amplitude norms (they are equalities; the part evaluates them exactly), 1.1 % in the
   constant 12, 1.4 % in 39.

## Parts as integrated (2026-11-17)

Four proof agents (AI agents of the same model family as the lead), one per part, were launched together with the
route referee (launch record with the SHA-256 of each brief: session log). Each worked in the lead's scratch from the
blueprint, this route and its brief, and wrote one Lean file; none wrote in the repository. The lead recompiled each
file with its final theorems ascribed to the blueprint proposition or frozen statement, printed the axioms (all:
propext, Classical.choice, Quot.sound), compiled the four files with the assembly and the four final theorems as one
scratch file, and copied the files in unchanged.

| Part | File | Lines | SHA-256 of the file as delivered | Deviations from the route (agent's report, in the lead's words) |
|---|---|---|---|---|
| HW1 `HadamardKernelRecFacts` | `OscInt/Front/HadamardWalkKernelRec.lean` | 132 | 6b9d1471e0bd254faf945793578741db7d3965839621d9c2c7a24d34e9bb7f0b | the recursion is proved on the numerators only (the denominator is a common factor and is never evaluated); K(0, ·) and K(1, ·) are taken from the first sanity layer, which the file imports; one new definition, the integrand |
| HW2 `HadamardPhaseFacts`, `HadamardAmplitudeFacts` | `OscInt/Front/HadamardWalkPhase.lean` | 402 | 1618290be509529e873442f0cea68de6d898736e78bb696b60461bb30c6d7928 | none in the mathematics; two new definitions (the real amplitude and its derivative); two arcs computed, two by the period π |
| HW3 `HadamardKernelBoundStatement` from the two propositions of HW2 | `OscInt/Front/HadamardWalkKernelBound.lean` | 348 | bc7481c49b75248ddf1d6618851e1e85f891dd79473c43c50c2da5f410c75567 | the first constant goes through √(2/(3√3)) ≥ 31/50 (margin 0.13 %) in place of a real-power identity, so the first numerical inequality reads (1600/31)(√2 − 1/√3) ≤ 14π (coefficient 6.88 ≤ 7) |
| HW4 `HadamardDecayArithFacts`, `HadamardLinearFacts` | `OscInt/Front/HadamardWalkLinear.lean` | 161 | 2a70338f5f5d972d6486d02095624d78a9c92bdb9047501e7f274c52e835f29b | 2^{1/3} ≤ 1.26 inside a helper (final constant 38.456 ≤ 39); H8 as an induction on an equality of states; one Mathlib name of the brief corrected |

Two agents (HW1, HW2) could not write their report file and returned the report as text. No agent reported a git
command (the launch messages forbade every git command by name).

Final theorems: `OscInt/Front/HadamardWalkFinal.lean`. The proof of HW-R (through HW1) uses two data lemmas of the
first sanity layer, `hadamardKernel_zero` and `hadamardKernel_one`, and four identities of the dispersion relation
proved there; HW-K uses the proved S1.2 and S1.3 (`OscInt.vanDerCorput_two`, `OscInt.vanDerCorput_three`, machine-
checked as stated since v0.1).
Checks by the lead at integration (2026-11-17, `docs/replay/2026-11-17-HW-integration-checks.txt`): `lake build`
completed; `StatementTypes.lean` asserts the four types (82 lines TYPE-OK); `leanchecker` on each of the ten HW
modules: exit code 0; the consumer example compiles. Not yet done at this point: the post-proof reviews and the
isolated replay.
