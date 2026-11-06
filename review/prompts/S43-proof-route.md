# Referee the proof route and blueprint for S4.3

You are a fresh, hostile, competent analyst. Read `docs/statements.md` (S4), `OscInt/Statements/D4Limit.lean`,
`docs/proof-S43.md`, `Blueprint/D4Limit.lean` and `OscInt/D4/ConstantPos.lean` (the assembly, already checked by Lean
against C1–C5 as hypotheses), `GammaFree.lean`, and Mathlib sources. Read no other proof file. Do not compile;
write nothing in the repository.

The assembly being machine-checked means C1–C5 suffice. Decide whether each of C1–C5 is TRUE as stated in Lean
(watch `Real.rpow` at 0 and for negative bases, `deriv` of non-differentiable functions, interval-integral
orientation for `a ≤ b`, `IntervalIntegrable` versus `IntegrableOn`), whether the route's argument for each is
correct, and whether a Lean proof can avoid every constant `GammaFree.lean` forbids (name the Mathlib lemmas you
expect a prover to need and say if any is proved through Gamma/Beta/Mellin). Also: is "integration by parts, then
pairing the humps of sin with the decreasing weight u^{-4/3}" an alternating-series argument in the sense of the
brief ("prove c_C ≠ 0 via ∫₀^∞ cos(u) u^{-1/3} du > 0 by an alternating-series argument; do not rely on Mellin/Gamma
identities")? Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text; a verdict line: can C1–C5 go to
proof agents as they stand? First line: `git rev-parse HEAD`.
