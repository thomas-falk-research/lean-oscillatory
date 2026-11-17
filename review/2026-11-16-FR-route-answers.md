# Answers to the route referee of batch FR (2026-11-16)

Subject: the route `docs/proof-FR.md`, the blueprint `Blueprint/FiniteRing.lean` and the lead's compiled assembly
`OscInt/Front/FiniteRingAssembly.lean`, as committed in 6ef8939, before any part was proved. One fresh-context
referee, read-only, on a snapshot of those files with the frozen statements, the interface checks and the library
files of batch PA that the route cites. It proved nothing and was not allowed to run Lean: that the assembly compiles
rests on the lead's build and on `make quick` (session log, 23:13:32Z), not on it. Lead and referee are AI agents of
one model family. The brief and the report are not recorded verbatim (rule 19); their SHA-256 values are in the
session log, and the findings are stated here in the lead's words. No calibration packet with planted errors was
given in this round.

Verdict: sound after corrections. No BLOCKER, no MAJOR; one MINOR; five NIT. The referee recomputed every display
of the ten parts, tested FR-S, FR-P, FC-P, FC-K and the two propagators numerically with its own scripts (120
digits; matrix exponentials for the propagators), could not falsify any of the five blueprint propositions, checked
that the types of the assembly compose to the seven frozen statements, and found every cited Mathlib and library
name in the sources.

| Finding | Severity | Answer |
|---|---|---|
| F-coset: the route writes the modulus of v on the strip as e^{−2t sin x sinh y − ry}; the sign in front of 2t is wrong (it is +2t sin x sinh y − ry; the library's own lemma on the kernel integrand has the right sign). The bound e^{2\|t\| sinh 1 + \|r\|} and everything after it are unaffected, but a prover who transcribed the display would be proving a false equality. | MINOR | Accepted; an error of the lead. Route revision, item 1; the proof brief of the part carried the correction, and the part does not compute the modulus at all (next row). |
| F-coset re-derives facts the library has: write v = e^{−2it} · e^{i(2t) cos z} · e^{irz} and use the proved periodic-analyticity and bound of the middle factor. | NIT (feasibility) | Accepted; the part was proved this way. Revision, item 2. |
| `RingEvenFacts` is stated for every N; the route argues for N ≥ 1 only (true at N = 0, both sides 0). | NIT | Accepted; the part has the case split. Revision, item 3. |
| F-images needs a two-sided majorant with different constants on the two sides; the symmetric lemma of batch PA cannot be reused as it stands. | NIT (feasibility) | Accepted; the part rebuilds it from two geometric series. Revision, item 4. |
| The index shift in the ring energy is one lemma about sums over a period; the derivative of the energy is easiest in the complex form Σ conj(w) w. | NIT (feasibility) | Accepted; both energy parts use the complex form. Revision, item 4. |
| A sentence of the route's header ("Referee B's remark … was checked against F-images: its majorant sums to exactly the right side") says nothing: that the majorant sums to the right side is the proof of F-images. What is true: for the extremal sequence the bound of F-images is an equality whenever \|r\| ≤ N. | NIT | Accepted; the sentence is replaced by the true one. Revision, item 5. |

Not verified by the referee, by its own account: that the assembly compiles; the dates and stamp names in the
route's header.
