# Answers to the blind pre-proof reviews of batch HC (TdF, TdE′)

Two fresh-context referees, A and B, reviewed the frozen statements at 80a8f50 (stamp
`stamps/20261112T120616Z-c56beb57ff8c`) against `docs/statements.md`, Batch HC. Both are Claude instances, like the
lead. Neither saw a Lean proof of an HC statement; none exists. Their prompts and reports are not recorded (owner
privacy rule, lessons 46). Each finding is restated below in the lead's words. Written by the session-10 lead.

## Verdicts

| Statement | Referee A | Referee B |
|---|---|---|
| TdF | FAITHFUL, TRUE | FAITHFUL, TRUE |
| TdE′ | FAITHFUL, TRUE (given T0E′, proved) | FAITHFUL, TRUE |

There is no BLOCKER and no MAJOR, so no statement changes and the stamp stands.

Both referees checked by compilation that:
- the volume on `Fin d → ℝ` is `Measure.pi` (`rfl`), and is the Dirac mass for d = 0;
- the phase parses as `t·(Σ cos) + Σ x·k`;
- `-(d : ℝ) / 3` is real division of the cast;
- the constant's `^ d` is a natural power;
- the integrand is integrable on the box, so no junk zero is possible.

Numerically, d = 2 and d = 3 kernels computed without factorising agree with ∏ I to 1e−14, and the d = 3 ratio to the
bound is at most 0.131.

## Findings and answers

1. **No datum with 3 ∤ d (A MINOR 1, B MINOR 2).** As a result, a rate with natural-number division `t^{−⌊d/3⌋}` and a
   constant copied from d = 3 would compile against every sanity theorem.
   - Fixed: `hypercubicCubeRoot_two` (d = 2, t = 8), `hypercubicCubeRoot_one_thr` (d = 1, t = (31/20)³, non-trivial
     regime) and `hypercubicCubeRoot_zero` (d = 0).
   - The second plant run rejects both plants with exact semantic evidence (C*² and C*³/4 against C*²/4).
2. **Mutations of the kernel definition are invisible to the sanity layer (B MINOR 1).** Examples are the sign of `I`,
   `cos ↦ sin`, a time scale, and other boxes.
   - Agreed, and recorded as NOT DETECTED in the plant record and the sanity docstring.
   - Every mutation that changes the kernel makes TdF false, so the TdF proof catches it. The box mutations are harmless
     for integer x.
3. **The TdF-time rejection was script-only (A MINOR 2, B NIT 3).** Agreed: it is now recorded as NOT DETECTED.
4. **Docstrings claimed detections that were never tested (A NIT 3).** The claims were "a coordinate used twice" and the
   threshold at t = 1/8. B adds that the t = 1/8 conclusion follows from the trivial bound. Corrected in the docstrings.
5. **The generator docstring named the LE2 files (B NIT 4).** Corrected.
6. **"In every dimension" should be "every d ≥ 1" (A NIT 5).** At d = 0 both sides equal the trivial bound. A
   clarification is added to `docs/statements.md`.
7. **The prior-art verdict ANTICIPATED is right (A).** The arXiv abstract of Stefanov–Kevrekidis states the rate.
