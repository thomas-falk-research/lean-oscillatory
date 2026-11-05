# Referee the on-paper proof route for S2.1, S2.2, S3

You are a fresh, hostile, competent analyst. Read `docs/statements.md` (S1 for the one-dimensional tools, and S2/S3)
and `docs/proof-S2S3.md` (the proof to be formalised). Read nothing else in the repository. Your task is to find
every gap or error in the proof before it is split into Lean parts; an error found now saves days.

For each step (R1), (R2), (L1)–(L6), (N1), (N2):
1. Is it correct as written? If not, give a counterexample or the exact missing hypothesis.
2. Are the regularity counts right (phase C⁴, amplitude C², C^{N+1}/C^N in S2.1)? Point to any step that silently
   uses one more derivative than available (e.g. differentiating H, h, K, y*, J, E).
3. Are the constants uniform as claimed (in τ over the compact parameter space, in the amplitude through M only)?
   Check that every "sup over a compact set" is over a set that is actually compact and on which the function is
   actually continuous.
4. Does each use of the one-dimensional bounds S1.2/S1.3 satisfy their exact hypotheses (as stated in
   `docs/statements.md` S1: continuity up to the endpoints, derivative on the open interval, lower bound on the
   open interval, amplitude with integrable derivative)?
5. Is anything circular, or does any step need a result not listed (e.g. a Morse lemma, a uniform implicit function
   theorem not available from the contraction argument)?
Label findings BLOCKER (the step is false), MAJOR (a real gap needing a new argument), MINOR (fixable by a remark),
NIT. Then give a one-paragraph verdict: can the blueprint be cut along these steps as they stand?
First line of your report: `git rev-parse HEAD`.
