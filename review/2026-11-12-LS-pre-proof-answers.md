# Answers to the blind pre-proof reviews of batch LS (LS-E, LS-K, LS-D, LS-D′)

Two fresh-context referees read the frozen batch at f59bd86, before any Lean proof of these statements existed. Referee
A checked fidelity, and referee B checked the mathematics.
- Both are Claude instances, like the lead.
- Their prompts and reports are not recorded (lessons 46). Each finding is restated below in the lead's words.
- Neither ran Lean, and nothing was committed while they read the tree (lessons 16). Written by the session-10 lead.

| Referee | Launched at commit | Launched | Finished | Run time |
|---|---|---|---|---|
| A (fidelity) | f59bd86 | 22:10:44 | 22:18:24 | 460 s |
| B (mathematics) | f59bd86 | 22:10:52 | 22:13:48 | 176 s |

## Verdicts

| | Referee A (fidelity) | Referee B (mathematics) |
|---|---|---|
| LS-E | FAITHFUL, scope full | TRUE |
| LS-K | FAITHFUL, scope full | TRUE |
| LS-D | FAITHFUL, scope full | TRUE |
| LS-D′ | FAITHFUL, scope full | TRUE |

No BLOCKER or MAJOR. The statements and the stamp `stamps/20261112T215742Z-d18e0780abdb` stand. Every finding is against the
sanity layer, the plant record or the planned route.

**Referee A.**
- **Kernel, by computation.** It checked the kernel formula, its sign, normalisation, gauge and factor 2 against
  matrix exponentials:
  - d = 1 with a generic 7-site datum, and d = 2: errors ≤ 1e−15;
  - the wrong sign, wrong gauge and time-scale variants are O(1) wrong at t ≠ 0 and invisible at t = 0.
- **Envelope, by computation.** LS-D implies LS-D′ on a grid, for d = 0..5.
- **The sanity data are true:** |J₀(8)| = 0.172 against the bound 0.774, and |J₀(14)| = 0.171 against 0.709.

**Referee B.** It derived the kernel from the Fourier symbol of Δ by hand, together with:
- absolute convergence (Parseval, or the factorial bound on Bessel coefficients);
- uniqueness (Δ is bounded, so the linear ODE is unique);
- negative t (K_d(−s, z) = conj K_d(s, −z), and K_d is even in z);
- |G_d| ≤ 1, and the LS-D′ envelope algebra (τ ≤ s if and only if τ/s ≤ (1 + τ)/(1 + s)).

Numerically:
- matrix exponentials match the kernel convolution to 3e−15;
- the bounds hold in d = 1, 2, 3, 6, 12 and for an infinitely supported ℓ¹ datum;
- the per-dimension factor in LS-D is 1.547, against the true 0.786 (Landau's constant), a ratio of about 1.97.

## Findings and answers

### Referee A

1. **MINOR, agreed and corrected: three plants were misclassified.**
   - D-rate, D-const-half and Dp-rate strengthen the bound. They were "rejected" only because a script step failed,
     and the planted conclusion still holds on the datum. So they are NOT DETECTED (lessons 44, 47), as batch HC
     classified a faster rate.
   - The referee showed that all three are false, with explicit data. Its sharpest case: the half constant fails by
     about 1.6% at t ≈ 0.392, by Landau's constant.
   - `docs/replay/2026-11-12-LS-sanity-plants.txt` gains a corrections section. The original run output is kept as
     recorded.
2. **MINOR, agreed: the sanity layer did not see the time dependence or the Laplacian.** Added, without any statement
   change:
   - `const_not_solution`: the constant curve δ₀ is not a solution, since its derivative is 0 but iΔδ₀(0) = −2i. This
     makes the derivative clause and the diagonal term of Δ bite.
   - `kernel_deriv_zero`, `kernel_deriv_zero_origin` and `kernel_deriv_zero_e1`: from LS-E and LS-K alone, the map
     t ↦ G_1(t, x) has derivative iΔδ₀(x) at t = 0, which is −2i at the origin and i at e₁.
   - The referee's full pin would compare these with an unconditional derivative of the kernel as defined. That needs
     differentiation under the integral. It is part of the proof of LS-K (the route's P-series gives it), so it is not
     added to the sanity layer.
   - The Laplacian mutations are listed as not planted in the plant record.
3. **MINOR, noted: K-time-scale is not detected at t = 0.** The plant record says so. The derivative theorems of
   item 2 state what the statements imply at t = 0, where the factor 2 is visible (i rather than i/2), but they do not
   refute the plant semantically.
4. **NIT, done: no compiled d = 0 instance of LS-D.** Added `dispersive_dim_zero`. `kernel_zero_time` already covers
   every d, including 0.
5. **NIT, done:** the docstring of `dispersive_one` now matches its conclusion.
6. **NIT, done:** the sanity header says that the sign of i is invisible to LS-D and LS-D′ (|conj G| = |G|) as well as
   to LS-E.

### Referee B

1. **MINOR, agreed: the x − y versus x + y orientation.**
   - Swapping x − y for y − x is harmless, since K_d is even in z. A y − x plant would not be a control and is not
     counted as one.
   - The x + y plant is meaningful but invisible on δ₀. Added `kernel_zero_time_shift`, on the datum δ_{e₁}, and the
     plant K-plus. Its witness (LS-E implies that the planted LS-K is false) uses δ₀ and δ_{e₁}: under the plant,
     G(0, 2e₁) would be both 0 and 1. Second plant run recorded.
2. **MINOR, agreed: the route must say where the ℓ¹ bound on G_d(t, ·) comes from.** TdE′ gives only a supremum bound.
   The route (docs/proof-LS.md, to be committed after this file) gets it from the series G_d(t, z) = Σₙ (it)ⁿ/n! Lₙ(z)
   with stencil powers Lₙ of ℓ¹ norm at most (4d)ⁿ, so ‖G_d(t, ·)‖₁ ≤ e^{4d|t|}. No Parseval is needed.
3. **NIT, done:** clarification 1 below repeats for LS-D′ that it beats the trivial bound only for |t| > τ.
4. **NIT, noted:** the constant is not sharp (factor about 1.97). That is consistent with the claim of "an explicit
   constant".
5. **NIT, noted:** a gauge plant needs 2dt ∉ πℤ. At t = 0 every gauge and kernel plant is invisible. The derivative
   theorems of A2 are at t = 0, but they concern derivatives, where these are visible.
