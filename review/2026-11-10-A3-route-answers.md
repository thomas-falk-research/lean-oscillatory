# Answers to the batch-A3 route referee (2026-11-10)

Subject: the route `docs/proof-A3.md`, the blueprint `Blueprint/Cusp.lean` and the compiled assembly
`OscInt/Cusp/Assembly.lean`, all at db4cc7d, before any part was proved. One fresh-context referee, read-only; it wrote
no proofs. Its prompt and report are not recorded (lessons 46); its findings are stated here in the lead's words.

## Verdict

No BLOCKER. Every blueprint part is true exactly as written in Lean, and the assembly proves S5.1′ and S5.1 from
them.
- **The parts:** `VdC4Facts`, `CoreEstimate4Facts`, `NormalPoint4` with `NormalizedData4Facts`,
  `TransverseNonStatFacts` and `A3NormalizeFacts`.
- **The assembly:** `δ` and `C` are fixed before `A, M, y, t`, and both support boxes contain the amplitude's
  support.
- **Its checks:**
  - It re-ran `#print axioms` on the assembly: `propext`, `Classical.choice` and `Quot.sound` only.
  - It `#check`ed every cited name.
  - It confirmed that `CoreHyps 4` is satisfiable, so P2 is not vacuous.
  - Two SymPy checks agree with the route: the reduced fourth derivative at the normal point, and the value of `G4`
    built from the repository's own `Y1`, `Y2` and `G3`.

## Findings

| Finding | Severity | Answer |
|---|---|---|
| P3: the joint continuity of an `fderiv`-defined `G4` does not follow from `FamilyCk 4` by composition, so "follow `continuousAt_G3`" will not work. | MAJOR (route step, not a statement) | Accepted. The explicit route (G4 as the derivative of `G3` along the graph, written with fourth derivatives) is now the plan; see `docs/proof-A3.md`, revision section. The lead had listed this as a risk; the referee's reading makes the explicit route necessary. |
| P2: `g` is C⁴ only on `Ioo (−a) a`, where the critical-curve condition of `CoreHyps` holds, not on `Ioo (−2a) (2a)`. | MINOR | Accepted. That interval suffices; the route names the lemmas. Checked against the `CoreHyps` definition. |
| P2: in `oscInt2_eq_iterated`, `γ` is the outer phase, not the curve. | MINOR | Accepted; the application is corrected in the route. |
| P4: the inner integral runs over `[−2b, 2b]`, but the gradient bound holds only on `[−b, b]`. | MINOR | Accepted: cut the inner integral to `[−b, b]` first, or use `integral_prod`. |
| P5: the third-derivative entry needs a permutation of arguments, and Mathlib's permutation lemma requires an analytic function here. | MINOR | Accepted: permute with `dd_comm` (lessons 12 explains why the Mathlib lemma does not apply). |
| `VdC4Facts` is not a hypothesis of the assembly. | NIT | Accepted; stated in the route. |

## Not checked by the referee

- Lean proofs of the parts; feasibility was judged by reading.
- The hand proof's explicit constants (2432, U), which the Lean route does not use.
- Stamps, pins, and the fidelity of the frozen statements themselves.

Next: proofs of the parts (CONTRIBUTING step 7). P1, P4 and P5 have no dependencies; P2 needs P1; P3 is the largest.
