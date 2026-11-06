# Referee the on-paper proof route and blueprint for S4.1

You are a fresh, hostile, competent analyst. Read `docs/statements.md` (S2/S3 for S2.1 and S3, S4 for S4.1),
`docs/proof-S4.md` (the route), `Blueprint/D4.lean` (parts D1–D9, definitions only) and the statement files
`OscInt/Statements/StationaryPhase.lean`, `OscInt/Statements/D4.lean`. You may read `OscInt/D4/Assembly.lean` (the
assembly, already checked by Lean against D1–D9 as hypotheses) and Mathlib sources. Read no other proof file. Do
not compile anything (other agents are using the machine); write nothing in the repository.

The assembly being machine-checked means D1–D9 suffice. Your job is whether each part is TRUE and provable as
stated in Lean, before agents spend days on a false one. For each of D1–D9:
1. TRUE / FALSE as stated in Lean. If false, a counterexample (watch Lean conventions: `x / 0 = 0`, `Real.rpow` of
   negatives, `fderiv` of non-differentiable functions is 0, the max norm on `ℝ × ℝ`, `tsupport`, `Icc` subtypes,
   Bochner integrals of non-integrable functions are 0).
2. Hidden hypotheses or regularity counts: does D2 really hold with `C⁴` and joint continuity of all derivatives of
   order ≤ 4 over `ε ∈ ℝ` including `ε < 0` and `ε = 0`? Does D3 need `disc ≠ 0` only? Does D4 need `C³` (symmetry
   of second derivatives, multilinearity of `ddd` in its slots)? Is `FamilyCk 3` enough for D5?
3. The rough size and the main Mathlib obstacles of a Lean proof of each part.
Label findings BLOCKER (false) / MAJOR (real gap) / MINOR / NIT, quoting the Lean text. End with a verdict: can the
parts be handed to proof agents as they stand? First line of your report: `git rev-parse HEAD`.
