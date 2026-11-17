# Answers to the route referee of batch VC2 (2026-11-17)

Subject: the route `docs/proof-VC2.md`, the blueprint `Blueprint/SecondDerivSharp.lean` and the lead's compiled
assembly `OscInt/Front/SecondDerivSharpAssembly.lean`, as committed in fbffce5. One fresh-context referee on a
snapshot of those files with the frozen statements, the interface checks and the files of batch S1 that the
assembly uses. It proved nothing and was not allowed to run Lean: that the assembly compiles rests on the lead's
build and on `make quick` (session log, 02:39:57Z). Lead and referee are AI agents of one model family; no
calibration packet was given. The brief and the report are not recorded verbatim (rule 19); their SHA-256 values
are in the session log. Isolation was by instruction: the packet was a snapshot inside the lead's scratch
directory and the referee was told to read nothing else there (lesson 61). As for batch HW, the six proof agents
were launched together with this referee, not after its report; it found nothing that required a part to be
redone. This route, in its present form, had not been refereed before.

Verdict: sound, for V1 to V9, the five blueprint propositions and both assembly theorems. No BLOCKER, no MAJOR; two
MINOR; six NIT. By its report the referee recomputed every formula by hand, confirmed the coefficients of V8 and
max B = 3.364571 in exact rationals, found no violation of V-root, V-head, V-tail or V-side on 6000 random
piecewise-quadratic sides with exact Fresnel integrals (reaching equality in V-side to 1e-16), re-ran the lead's
script with identical output, and confirmed the Mathlib names by grep.

| Finding | Severity | Answer |
|---|---|---|
| V8 leaves the subdivision unspecified. With the route's rule, 200 uniform cells fail (bound 3.544) and about 400 are needed (3.452), or 62 adaptive ones; the right end must be a rational R with R²/2 ≥ π; for the sine bound, steps from a Mathlib bound are cheaper than the Lagrange remainder. | MINOR (feasibility) | Accepted. The part VC5 had been launched with the route's rule as a suggestion and the freedom to choose; it chose chords and tangents (six cells) and seven steps from Mathlib's cosine bound. Route revision, item 1. The lead has not re-run the referee's cell counts. |
| The cited `primitive_hasDerivOn` is for the complex integrand only; V3 and V4 need a real analogue; one shared helper would avoid proving it twice. | MINOR (feasibility) | Accepted. The parts VC2 and VC3 each proved what they needed (VC3 as a lemma, VC2 inline); they are not merged, because the parts are kept as delivered. Revision, item 2. |
| V2 and V4 state hypotheses stronger than they use. | NIT | Noted in the revision, item 3; the blueprint propositions are unchanged. |
| V4: the induction must be generalised over the side. | NIT | The part does so. |
| V5 does not say how n is chosen. | NIT | n = ⌈(θ − π/2)/(2π)⌉; revision, item 3. |
| V3: the body of the proof assumes c < d. | NIT | Revision, item 3. The part needs no case split. |
| The blueprint docstring of `Vdc2HeadFacts` says "with equality for the quadratic phase" without the condition f(d) − f(c) = w. | NIT | Docstring corrected at integration (the blueprint file changed in that one comment; the proposition did not). |
| The lead's interface script comes near equality in V-side only in its last line; it is weak evidence for the tightness of the choice of w. | NIT | Accepted as a limit of that script; the referee's own test is not in the tree. |

Not verified by the referee, by its own account: that the blueprint and the assembly compile.
