<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch K2: answers to the route referee (2026-11-28)

Written by the lead. The route referee read `docs/proof-K2.md` at 8023f6b and the blueprint draft (scratch). That was
after the answers to the blind pre-proof reviews were stamped (`stamps/20261128T023440Z-e368c37563ab`). It ran in a
fresh context, of the lead's model family: harness 960 s, 45 tool uses, brief SHA-256 in
`docs/progress/2026-11-28-session16-log.md`. It compiled probes in its own scratch, one Lean process at a time, and
wrote nothing in the repository. The report is not reproduced; findings are in the lead's words.

**Verdict: proceed after changes. No FATAL finding.** All twelve blueprint propositions of the draft are true as
written and no weaker than their assemblies need. Every assembly reaches its frozen statement with the existing names,
which R `#check`ed in full, once the repairs below are made.

Probes:
- the blueprint elaborates with `import OscInt` and `import Blueprint`;
- P9 at n = ⊤ gives `ContDiff ℝ ∞`;
- P13's `Icc (0 : ℝ × ℝ) 1` is the unit square;
- `SliceHyps` carries only `ContDiff ℝ 4`;
- the new P14 elaborates, and a numerical check of its identity with normalisation `(4π²)⁻¹` agrees to 2.2e−16.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| M1 | MAJOR | P2's plan uses `ImplicitAux.exists_coreHyps` unchanged. Its `hG` must hold for every `SliceHyps` phase, which is only C⁴, so the order-6 identity cannot be proved there. Its output is `CoreHyps` with a C³ root under `∃`. | Accepted. Route section 8, item 1: R's operator route (q-independence of D; identity along any critical curve; a C^∞ slice lemma), or a clone `exists_coreHypsM`. P2's proposition is unchanged. |
| M2 | MAJOR | The torus transfer of K2-F (rescaling, measure, reindexing, lifting) has no part. | Accepted. New part P14 `TorusExpansionFacts`, R's compiled form, proved by pointwise inversion and `integral_tsum`; route section 8, item 2. |
| M3 | MAJOR (sketch; proposition true) | P11's cutoff as sketched is not localised (b₂(w) = 1 along the whole curve) and not smooth where R or R_m change sign. | Accepted. Smooth substitutes on the sign-fixed range, a spatial plateau ζ, and `integral_deriv_smul_comp` for the complex integrand; route section 8, item 3. |
| m1 | MINOR | P5 cannot go through a pointwise `ContDiffAt ℝ ∞`; it needs the slice uniqueness argument. | Accepted; P2, P5, P6 go to one agent with the shared C^∞ slice lemma. |
| m2 | MINOR | P3 is missing from the agent list. | Fixed (section 8). |
| m3 | MINOR | Part dependencies are unstated. | Fixed: P11 and P12 take P9 as a hypothesis. |
| m4 | MINOR | Nine Mathlib names are not in `MathlibNames.lean` (rule 12). | Fixed; all resolve at the pin. |
| m5 | MINOR | K2-D's witness at `(π/2, π/2)`: g′ by `hasDerivAt_reducedFn`, g″ by P6 and the kernel; at A5 the spanning condition by `span_of_hyps`. | Accepted (section 8, item 4). |
| m6 | MINOR | The nondegenerate case needs `hessDet · (v₁w₂ − v₂w₁)²/D²[w, w]`, not "det/D²[w, w]". | Accepted. |
| N1–N7 | NIT | `phase_eq` at k₀, `lin (0, q)` form, `max C 0`; the CosMoment name; P9's parameter type; a cheaper P13; a shared monomial-coordinate lemma; the blueprint docstring; lowerCamel names. | All taken (section 8, item 4; the committed blueprint's docstring). |
