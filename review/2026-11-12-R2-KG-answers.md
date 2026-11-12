# Answers to the external reviewer's R2 packet (discrete Klein–Gordon kernel), 2026-11-12

Subject: one packet from the same external reviewer as `review/2026-11-10-external-followup-answers.md`, against this
branch at 39408fd and `main` at f63458b. It answers target R2 ("explicit constants beyond the square lattice") of the
lead's research prompt; the reviewer chose the target. The packet, the prompt and the chat are not recorded (owner
privacy rule, lessons 46). Each claim is restated below in the lead's words, with the evidence the lead produced.
Written by the session-10 lead.

## The claim, in the lead's words

For the one-dimensional discrete Klein–Gordon dispersion ω_m(k) = (m² + 2 − 2 cos k)^{1/2}, let

  J_m(t, ξ) = ∫_{−π}^{π} e^{i(t ω_m(k) + ξk)} dk,  a_m = ((m² + 4)^{1/2} − m)/2 = 2/((m² + 4)^{1/2} + m),

so a_m is the maximum group velocity (a_0 = 1, a_m ≈ 1/m for large m), and C* = 8(1 + √7)/3 is the T0E′ constant.

1. **Main bound.** For every m ≥ 0, real t ≠ 0 and real ξ: |J_m(t, ξ)| ≤ min{2π, C* (a_m |t|)^{−1/3}}.
2. **Uniform in the mass.** Fix m₀ > 0. For every m ∈ [0, m₀]: |J_m(t, ξ)| ≤ C* a_{m₀}^{−1/3} |t|^{−1/3}. This beats
   the trivial 2π exactly for |t| > γ/a_{m₀}, γ = (C*/(2π))³ = 3.70448…; |t| ≥ 3.705/a_{m₀} suffices, and for m₀ = 1
   the threshold is 5.99398…, so |t| ≥ 6 suffices. (Corrected in the addendum: the first version gave the
   downward-rounded "3.704/a_{m₀}" and "|t| > 5.99", which are approximations, not sufficient conditions.)
3. **The mass factor is necessary.** At t = 1/(2a_m), |J_m(t, 0)| ≥ 7π/4. So the best constant C_opt(m) in
   |J_m| ≤ C_opt(m) |t|^{−1/3} satisfies 4.3636 a_m^{−1/3} ≤ C_opt(m) ≤ 9.7220 a_m^{−1/3}. No single constant works for
   all masses.

Only the "half-wave" kernel e^{itω} is covered. The full Klein–Gordon solution also has the multiplier sin(tω)/ω, and at
m = 0 that part does not decay.

## How the proof works

The packet carries the LE2 proof over to the new phase. The key new fact is an exact level-set identity. Set
h = ω_m′/a_m and q = a_m². Then h(k) = sin k / (1 + q² − 2q cos k)^{1/2}, with maximum 1 at k = arccos q. For
−1 < r < 1, the set {k ∈ [−π, π] : h(k) > r} has length exactly 2 arccos r, **for every mass**. The end points of the set
move with m, but their distance does not. These are the same lengths as for sin k, which is what the LE2 band and cap
estimates use.

With T = a_m |t| and v = |ξ|/T, integration by parts then gives the five LE2 envelopes. Like the cosine phase, h rises
to 1 and falls back on each half-period.

## Verdict

**TRUE (hand proof, independently checked; not machine-checked).**

**The mathematics.** The lead re-derived the new parts:
- the mass identities and the formula for h and h′;
- the level-set endpoints and lengths;
- the integration-by-parts table, including the turning values;
- the reduction of signs, the passage m → 0 through |J_m − J_0| ≤ 2π|t|m, and the lower bound.

A fresh-context referee re-derived the whole proof and found no BLOCKER or MAJOR issue.

**What is already machine-checked.** The five envelopes are, term for term, the LE2 blueprint propositions
`BandLowFacts`, `BandHighFacts`, `CapLowFacts`, `CapHighFacts` and `WholeFacts` (`Blueprint/LatticeCubeRoot.lean`), with t
replaced by T and the cosine kernel by the KG kernel. The Lean proofs of the step from the envelopes to C* T^{−1/3} use
only those five hypotheses and the trivial bound 2π:
- `regime8_of` and `regime38_of` (`OscInt/Front/LatticeCubeRootRegime8.lean`, `OscInt/Front/LatticeCubeRootRegime38.lean`);
- `small_time` (`OscInt/Front/LatticeCubeRootAssembly.lean`).

The norm of the kernel appears there only as an opaque real number (checked by the lead and the referee). So that half
of the proof is already machine-checked for the cosine kernel, and a mechanical generalisation covers the KG kernel.

**How sharp the constant is.** The empirical best constant is about 5.18 a_m^{−1/3} at m = 0, falling to about 5.05
for large m, close to the cosine kernel's 5.05 (FLOAT; lead and referee agree). For the universal mass-normalised
coefficient, C* is within a factor strictly below 1.9 of the optimum (PROVEN-BY-HAND, exact arithmetic checked; see the
addendum).

## What the lead checked

**1. The packet's integrity.**
- The archive's SHA-256 matches the one the owner relayed.
- All 23 payload files match the packet's manifest, checked with the lead's own script rather than the packet's
  verifier.

**2. The packet's scripts, reproduced.**
- The lead read both scripts and the verifier before running them. They only compute, write to an output directory,
  and call the two scripts.
- They refuse to run except on CPython 3.12.14. The lead ran copies with only that version check removed, under
  Python 3.13.18, in a virtual environment holding the packet's pinned numpy 2.3.5, scipy 1.17.0, sympy 1.14.0 and
  mpmath 1.3.0.
- Exact checks: PASS.
- Numerics: PASS on all 471 cases. The maximum discrepancies (7.84e−9 between methods, 2.10e−8 on doubling) agree
  with the packet's record to every printed digit, and all four planted controls were rejected.

**3. The lead's own checks**, `numerics/review/kg_checks.py`, written without reusing the packet's code. Record:
`numerics/results-kg-checks-2026-11-12.txt`, RESULT PASS.
- **K1 (EXACT, sympy):** a²(m² + 2) = 1 + a⁴; the numerator of h′; 1 − h² = (cos k − q)²/(1 + q² − 2q cos k); both
  level-set roots. Also ω′′′(arccos q) = −a (FLOAT, 40 digits).
- **K2 (FLOAT):** the level-set length equals 2 arccos r, at three masses and five levels; the tolerance is 1e−4
  and the largest observed deviation 3e−6.
- **K3 (FLOAT):** max of (a_m|t|)^{1/3}|J_m|/C* = 0.5326, at m = 0, T ≈ 0.95, ξ = 0. This ratio is taken against
  the decaying term C*(a_m|t|)^{−1/3}, not against min{2π, ·} (against the minimum it tends to 1 as t → 0 at ξ = 0).
  - Masses: 0, 1e−6, 0.01, 0.1, 0.5, 1, 2, 5, 20.
  - Times: 45 normalised times from 0.1 to 2000.
  - Velocities: 522 values of v = ξ/T in [0, 1.6], refined at the caustic.
  - Discretisation: Gauss–Legendre split at the turning points; node doubling changes the values by at most 1.1e−11.
  - Empirical max T^{1/3}|J_m| per mass: 5.178 (m = 0), 5.169 (0.01), 5.123 (0.1), 5.158 (1), 5.106 (2), 5.060 (5),
    5.048 (20).
- **K4 (FLOAT):** |J_m(1/(2a_m), 0)| is between 5.897 and 5.990, against 7π/4 ≈ 5.498. The ratio
  |J_m − J_0|/(2π|t|m) is at most 0.202.
- **Controls, both rejected:** the bound without the mass factor at m = 20, and the faster rate T^{−1/2}.

**4. Fresh-context referee** (a Claude instance, like the lead; lessons 48):

| Referee | Launched at commit | Launched | Finished | Run time |
|---|---|---|---|---|
| R2 mathematics | 39408fd | 17:01:39 | 17:33:34 | 1919 s |

- Verdict: the main bound, the uniform corollary and the lower bound are TRUE. No BLOCKER or MAJOR issue.
- It re-derived Sections 2–9 by hand and with its own sympy and numpy code, including every row of the
  integration-by-parts table and the containment of each turning point in its piece.
- It tested the five envelopes at 1500 random points (m from 1e−6 to 30); the smallest margin was 1.8e−3, for W.
- It scanned the bound with two independent quadratures, which agreed to 2.6e−12. Its maximum ratio was 0.53294,
  at m = 0, T ≈ 0.91, ξ = 0, which agrees with the lead's K3.
- For large T the ratio tends to the Airy value, about 0.437.

**5. Prior art, spot-checked.** The lead read the relevant sections of the primary texts:
- **Stefanov–Kevrekidis 2005**, arXiv nlin/0409009v1, Theorem 2 and its proof, equations (7)–(9). The KG decay
  t^{−1/3} is proved at mass 1 only, uniformly over real slopes, with a non-explicit van der Corput constant.
- **Egorova–Kopylova–Teschl**, J. Spectral Theory 5 (2015), author manuscript, Lemma 7.1, (7.8) and Remark 7.2:
  - O(t^{−1/3}) for each fixed mass μ > 0, with a non-explicit constant;
  - the maximum velocity √κ with κ = (2 + μ² − (4μ² + μ⁴)^{1/2})/2, which equals a_m²;
  - non-decay of the free wave equation at μ = 0.
- **Hong–Yang 2019**: only the abstract and Theorem 1.5 were read, through a fetching agent. They give
  lattice-spacing-uniform Strichartz estimates with non-explicit constants.
- **Other sources:** the reviewer's further citations (Mielke–Patz, Xiong–Thiel–Barkai, Komech–Kopylova–Kunze,
  Wan–Zhang) were not re-read. The lead did not re-run the reviewer's 42-query search.

So the decay rate and the maximum velocity a_m are classical. Not found in the logged search: an explicit constant for
every mass, the uniform-in-mass form, and the level-set identity for m > 0.

## Findings on the packet

1. **MINOR (referee): Section 7 is a valid variant, not the Lean proof.** It uses a monotone sum of arcsines where the
   machine-checked LE2 route splits at v = 1/8, and 27/10 where Lean uses 673/250. Both are correct. A formalisation
   should reuse the Lean scalar layer through an abstract-envelope interface, not re-prove Section 7.
2. **MINOR (referee and lead): AI agreement is not independent evidence.** The packet's "independent re-derivation"
   was done by agents of the same model family, and the packet partly says so. The lead's own reviews are subject to
   the same caveat (`docs/prior_art.md`).
3. **MINOR (lead): the version pin is too strict to reproduce.** The verifier and scripts refuse to run except on
   CPython 3.12.14, so a reader without that exact interpreter cannot reproduce the packet. The lead reproduced it with
   the version check removed (item 2).
4. **NIT (referee):**
   - In branch W of Section 7.1, a normalised and an unnormalised quantity are written alike; the arithmetic is right.
   - The coefficient 11524/4275 in (6.6) is weaker than necessary.
   - (2.4) is not used.
5. **NIT (lead): the "useful from" threshold is for the uniform corollary.** For a single mass the bound beats 2π for
   a_m|t| > 3.704, the LE2 threshold in the variable T.

## Scope

- **Mathematics:** the half-wave kernel bound above, and nothing more.
- **Model:** the idealised linear Klein–Gordon chain. Examples are harmonic chains with on-site pinning, linearised
  coupled pendula, and the linear Klein–Gordon lattices of Stefanov–Kevrekidis and Egorova–Kopylova–Teschl. For
  integer sites n, J_m/(2π) is the e^{itω} part of the lattice propagator. The full solution also needs the multiplier
  sin(tω)/ω, which is not covered.
- **Engineering:** no device, simulation or control benefit is claimed by the packet or here.

## Proposed next step (owner decision)

The packet meets ROADMAP gates 2 and 3:
- **Gate 2:** an explicit statement, re-derived and refereed.
- **Gate 3:** a logged search with primary sources spot-checked; novelty wording "explicit constant for every mass,
  machine-checked if built; the rate and the maximum velocity are classical".

Gate 1 (need) and gate 4 are the owner's. It is recorded as a candidate in `docs/ROADMAP.md`. If promoted, the route
would be:
1. **Freeze** a batch with the main bound and the uniform corollary. Statement choices to make at the freeze:
   - t ≠ 0 with |t|, or t > 0 plus the symmetry;
   - with or without the trivial min{2π, ·}.
2. **Generalise** the LE2 scalar layer to an abstract kernel (mechanical; no frozen file changes).
3. **New parts:**
   - the h-geometry and level sets;
   - the integration-by-parts pieces for the KG phase;
   - the limit m → 0 and the assembly.

The new parts are of the same size as the LE2 pieces file.

## Addendum (2026-11-12, after an external audit of edc251c)

The owner relayed an external auditor's reading of edc251c (the same reviewer service; not recorded, lessons 46). The
auditor agreed with the verdict and the findings. It said a revised packet would carry a new version and hash; the
archive reviewed here stays the reviewed object. It added three points, each checked by the lead.

1. **A rigorous factor below 1.9 (adopted).** Define K(m) = sup over t > 0 and real ξ of (a_m t)^{1/3}|J_m(t, ξ)|, and
   K_univ = sup over m ≥ 0 of K(m).
   - K_univ is the best universal coefficient in front of (a_m|t|)^{−1/3}, and the main bound gives K_univ ≤ C*.
   - **Witness.** Take m = 0, t = 7/8, ξ = 0 and the centre b = 5/4. With ω₀ = 2|sin(k/2)|:
     - the moments are ∫ω₀ = 8, ∫ω₀² = 4π, so ∫(ω₀ − 5/4)² = 57π/8 − 20;
     - by |J| ≥ Re(e^{−itb}J) and cos u ≥ 1 − u²/2, valid for all real u,
       |J₀(7/8, 0)| ≥ 2π − (49/128)(57π/8 − 20) = 245/32 − 745π/1024 > 19245/3584, using π < 22/7.
   - **The chain.** With (239/250)³ < 7/8, this gives K_univ > (239/250)(19245/3584) > 5.13. With √7 < 53/20,
     C* < 146/15, so C*/K_univ < 2920/1539 < 1.9.
   - **Checks.** `numerics/review/kg_factor_check.py` checks the three moments symbolically and the rational chain
     exactly (record `numerics/results-kg-factor-check-2026-11-12.txt`, RESULT PASS). Numerically,
     (7/8)^{1/3}|J₀(7/8, 0)| = 5.17825, essentially the sweep's maximum 5.1781.
   - **Scope.** This bounds the universal mass-normalised coefficient only. It is not a factor-1.9 statement for the
     optimum at each fixed mass, nor for the unweighted constant on an interval [0, m₀]; the per-mass lower bound 7π/4
     still serves that purpose.
   - **Comparison.** For the cosine kernel, the rigorous ratio recorded for LE2 is 1.9706
     (`review/2026-11-11-LE2-post-proof-answers.md`).
2. **Threshold wording (corrected above).** "3.704/a_{m₀}" and "5.99" were downward-rounded, so they are not
   sufficient conditions. Exact: |t| > γ/a_{m₀} with γ = 3.70448…; sufficient: |t| ≥ 3.705/a_{m₀}, or |t| ≥ 6 for
   m₀ = 1.
3. **The Lean reuse boundary (agreed, made precise).**
   - The blueprint propositions name `latticeKernel1`. So a generic interface must be stated and compiled first: a real
     function R(T, v) with the five envelopes and R ≤ 2π as hypotheses, and R ≤ C* T^{−1/3} for T > 0, v ≥ 0 as
     conclusion. Then the cosine and KG kernels are separate instances.
   - The small-time step needs the KG kernel's own 2π bound, because the existing lemma unfolds the cosine integrand.
   - The cost estimates in this file are structural planning estimates, not compilation results.

