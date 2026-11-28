# Batch SPL-N: planted controls of the sanity layer (docs/lessons.md, rules 8 and 9)

Written by the sanity-layer agent for SPL-N on 2026-11-28 (generator run 2026-11-28T12:49:32Z to 2026-11-28T12:52:24Z
UTC, generator exit code 0; Python 3.13.18) against the draft statement text, unchanged:

- `OscInt/Statements/StationaryLeadingSharp.lean`, SHA-256
  aa3eb596a39389712f2d03159606b5abe66262b835a6fbd77b42a5bf594b06f8 (identical to the copy
  `stmt/StationaryLeadingSharp.lean` from which the generator reads the statement text; the module itself is the
  repository's built `.olean`). The repository commit was not read: the brief forbids every git command.
- Sanity layer `src/OscInt/Front/StationaryLeadingSharpSanity.lean` (module `OscInt.Front.StationaryLeadingSharpSanity`,
  namespace `OscInt.API.StationaryLeadingSharpSanity`, 46 theorems), SHA-256
  a7836434cc01e10c3156f430caccd15f472830122f07bb57fc33005817ec97fc.
- Generator `plants_spln.py.txt` (= `gen/plants_spln.py`), SHA-256
  81f1bc7a5edf0b994da9de48da41493943ad7d8c80a4dc0b83f22f09de4afc14.

Harness (as batch K2): `.lake/build/lib/lean/OscInt` mirrored (real directories, symlinked files; `gen/mirror.sh`,
SHA-256 f3fba085fcbcaec6e75a3b9e7018704fcabe19fe59530ce8c2309bfdead26e7f) into `lib/`, placed first on `LEAN_PATH`
inside the repository's `lake env` (`gen/lean.sh`, SHA-256 ed5ded11b70407717bd816673c50791ad0d9e82116460d14e6c4981f3f384645:
from `/home/user/lean-oscillatory`, `leanrun nice -n 10 lake env sh -c 'export LEAN_PATH="<lib>:$LEAN_PATH"; exec lean
-DautoImplicit=false …'`; Lean 4.35.0, Mathlib 56a005855ea1). The sanity module was compiled with
`lean.sh -o lib/OscInt/Front/StationaryLeadingSharpSanity.olean --root=src src/OscInt/Front/StationaryLeadingSharpSanity.lean`
(exit 0, no warnings). Each generated file imports `OscInt.Front.StationaryLeadingSharpSanity` only. One Lean process
at a time. Nothing in the repository was written.

Method (as batches SPL, TRI and K2). For each plant: `ok-` = unplanted copy `P_<Statement>` followed by copies
(renamed `P_`) of every sanity theorem that names that statement constant; must compile. `plant-` = the same with ONE
textual mutation; its rejection by the copied scripts is recorded and is never counted as a detection. `witness-` =
the planted copy and compiled theorem(s), with `#print axioms` (exactly one line per witness theorem, each
propext, Classical.choice, Quot.sound, checked by the generator). Kinds: `not` (¬ planted, from unconditional data
of the sanity layer and proved repository theorems) DETECTED; `rel` (draft statement of the batch → ¬ planted)
DETECTED RELATIVE TO THE TRUE STATEMENT; `weak` (draft → planted) TRUE WEAKENING; `char` NOT DETECTED, with a
compiled characterisation of what a detection would have to refute. No file proves, or uses a proof of, a batch-SPL-N
statement. Proved repository theorems used by witnesses (through the sanity layer): SPL-S `stationaryLeading`,
SPL-K `stationaryLeadingSevenEighths`, SPL-A `stationaryLeadingAttained`, and the batch-SPL sanity layer.

## Outcome

24 plants, at least one per statement and one per constant, exponent and hypothesis: 11 DETECTED (NU-b, NU-e, NL-a,
NL-b, NK-c, NK-d, NK-e, NK-f, NK-g, NK-h, NC-a), 4 DETECTED RELATIVE TO A TRUE STATEMENT of the batch and NOT DETECTED
unconditionally (NU-a via SPL-NL, NL-c via SPL-NU, NK-a via SPL-NC, NC-b via SPL-NK), 6 TRUE WEAKENINGS (NU-c, NU-d,
NL-e, NK-b, NC-c, NC-d; NU-c and NK-b are moreover proved outright, NU-d is equivalent to the draft, NC-d is
vacuous), 3 NOT DETECTED (NU-f, NL-d, NL-f; all three are false by a decimal evaluation of `κ`, see below). Every
statement has an unconditional detection. All 24 unplanted copies compile (identical output, exit code 0); all 24
planted copies are rejected by the copied scripts (script-only, not counted; NK-b's rejection is of a true
weakening).

| plant | statement | mutation | outcome | evidence |
|---|---|---|---|---|
| NU-a | SPL-NU | cap `360987/500000` ↦ `72197399/10⁸` | REL. (SPL-NL) / NOT DET. uncond. | SPL-NL's point exceeds the planted cap |
| NU-b | SPL-NU | cap ↦ `360987/5000000` (digit dropped) | DETECTED | proved SPL-S: `\|κ(τ)\| ≥ 3/10` at some `τ ≥ 0` (`spln_kernel_large`) |
| NU-c | SPL-NU | cap ↦ `7/8` | TRUE WEAKENING | draft → plant; plant proved outright (`spln_kernel_le_seven_eighths`, from SPL-A and SPL-K) |
| NU-d | SPL-NU | `∀ τ` ↦ `∀ τ ≥ 0` | TRUE WEAKENING (equivalent) | draft → plant and plant → draft (`\|κ\|` even) |
| NU-e | SPL-NU | `splKernel` ↦ `splKernelPos` | DETECTED | `\|κ₊(−2)\| > 3` (`spln_kernelPos_neg_two`: `κ₊(−τ) + κ₊(τ) = iτ²F(∞)`, `\|F(∞)\|² = π/2`, proved `\|κ₊(2)\| ≤ 7/8`) |
| NU-f | SPL-NU | cap ↦ `721973995/10⁹` (inside the window) | NOT DETECTED | compiled: plant → `\|κ(8123/5000)\| ≤ 0.721973995`; window `0.72197399 < 0.721973995 < 0.721974`; decimal `\|κ(8123/5000)\| = 0.72197399899…`, so false |
| NL-a | SPL-NL | point `8123/5000` ↦ `0` | DETECTED | `κ(0) = 0` (`spln_lower_fails_at_zero`) |
| NL-b | SPL-NL | value ↦ `72197399/10⁷` (digit dropped) | DETECTED | proved `\|κ\| ≤ 7/8` |
| NL-c | SPL-NL | value ↦ `72197401/10⁸` (above the cap) | REL. (SPL-NU) / NOT DET. uncond. | `spln_cap_excludes_higher_lower` |
| NL-d | SPL-NL | point ↦ `13/8` (`= 8125/5000`) | NOT DETECTED | compiled: plant ↔ ¬(`\|κ(13/8)\| ≤ 72197399/10⁸`); decimal `\|κ(13/8)\| = 0.72197396587…`, so false; needs an enclosure of width `< 3.4·10⁻⁸` |
| NL-e | SPL-NL | `<` ↦ `≤` | TRUE WEAKENING | draft → plant |
| NL-f | SPL-NL | value ↦ `7219739995/10¹⁰` (inside the window) | NOT DETECTED | compiled: plant ↔ ¬(`\|κ(8123/5000)\| ≤ 0.7219739995`), and `0.7219739995 < 0.721974`; decimal value `0.72197399899…`, so false |
| NK-a | SPL-NK | constant ↦ `7/10` | REL. (SPL-NC) / NOT DET. uncond. | SPL-NC at `c = 7/10` (`spln_sharpness_refutes`) |
| NK-b | SPL-NK | constant ↦ `7/8` | TRUE WEAKENING | draft → plant; plant = proved SPL-K |
| NK-c | SPL-NK | hypothesis `0 < λ` dropped | DETECTED | `λ = 0`: `0^{−3/2} = 0`, `\|R(G_1, 0)\| = √(2π)` |
| NK-d | SPL-NK | `λ^{−3/2}` ↦ `λ^{−1/2}` | DETECTED | `G_{1/2}`, `λ = 1/16`: plant `≤ 2.74`, `\|R\| ≥ 4.8` |
| NK-e | SPL-NK | `λ^{−3/2}` ↦ `λ^{−5/2}` | DETECTED | `G_1`, `λ = 100`: plant `≤ 2.8·10⁻⁵`, `\|R\| ≥ 1.24·10⁻³` |
| NK-f | SPL-NK | `‖g‴‖₁` ↦ `‖g″‖₁` | DETECTED | `G_4`, `λ = 1600`: plant `≤ 1.1·10⁻⁴`, `\|R\| ≥ 3.13·10⁻⁴` |
| NK-g | SPL-NK | hypothesis `SplAmplitude` dropped | DETECTED | the constant `1`, zero derivatives, `λ = 1`: `\|R\| = √(2π) > 0` |
| NK-h | SPL-NK | constant ↦ `360987/5000000` (digit dropped) | DETECTED | `G_1`, `λ = 4`: plant `≤ 0.0343`, `\|R\| ≥ 0.151` |
| NC-a | SPL-NC | range `c ≤ 72197399/10⁸` ↦ `c ≤ 7/8` | DETECTED | at `c = 7/8` the negated bound is the proved SPL-K |
| NC-b | SPL-NC | range ↦ `c ≤ 360987/500000` (the cap) | REL. (SPL-NK) / NOT DET. uncond. | at `c = 360987/500000` the negated bound is SPL-NK |
| NC-c | SPL-NC | range ↦ `c ≤ 72197/10⁵` | TRUE WEAKENING | draft → plant |
| NC-d | SPL-NC | inner `0 < λ` dropped | TRUE WEAKENING (vacuous) | draft → plant; plant proved for every `c` at `λ = 0` (`spln_sharpness_needs_pos_lam`) |

Why the window plants are not detected (NU-f, NL-d, NL-f). The two rationals are `10⁻⁸` apart, and the true values
sit inside: by a 60-digit decimal evaluation of the power series of `F` (not an enclosure; cross-checked to `10⁻¹⁴`
by Simpson quadrature in double precision, `numerics/`), `sup |κ| ≈ 0.7219739989980` at `τ ≈ 1.6246006`, i.e.
`1.0·10⁻⁹` below the cap, and `|κ(8123/5000)| ≈ 0.7219739989979`, `9.0·10⁻⁹` above the lower value. A cap or a
lower value moved inside this window, or a point moved off the super-level set `{|κ| > 72197399/10⁸} ≈ (1.624392,
1.624809)` (which contains only the grid points `8122/5000`, `8123/5000`, `8124/5000`), is refuted only by an
enclosure of `κ` to better than `10⁻⁸`, which is the content of SPL-NU and SPL-NL themselves (the 40-cell certificate);
the proved theorems give only `3/10 ≤ |κ(τ₀)|` at some point and `|κ| ≤ 7/8`. Why NU-a, NL-c, NK-a, NC-b are only
relative: each mutation moves a rational across the other one (NU-a, NL-c) or replaces a constant by one the other
statement pins (NK-a, NC-b); refuting them unconditionally needs a kernel enclosure (NU-a, NL-c) or a kernel lower bound
above `0.7` (NK-a), or SPL-NK itself (NC-b). Why the weakenings cannot be refuted: they are implied by the draft
(compiled), and three of them are proved or vacuous.

The decimal values are exploratory floating-point evidence for a NOT DETECTED verdict only; nothing in this record
or in the sanity layer depends on them.

## Generator log (SUMMARY.txt)

```
ok-NU-a: accepted (want accepted) [2.4 s]
plant-NU-a: rejected (want recorded) [2.6 s]
    first error: plant-NU-a.lean:13:2: error: Type mismatch
witness-NU-a: accepted (want accepted) [2.2 s]
  NU-a [the cap 360987/500000 ↦ 72197399/10⁸ (the two rationals confused)]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-NU-b: accepted (want accepted) [2.4 s]
plant-NU-b: rejected (want recorded) [2.1 s]
    first error: plant-NU-b.lean:13:2: error: Type mismatch
witness-NU-b: accepted (want accepted) [2.4 s]
  NU-b [the cap 360987/500000 ↦ 360987/5000000 (a digit dropped)]: DETECTED (witness compiled: ¬ planted statement)
ok-NU-c: accepted (want accepted) [3.0 s]
plant-NU-c: rejected (want recorded) [2.5 s]
    first error: plant-NU-c.lean:13:2: error: Type mismatch
witness-NU-c: accepted (want accepted) [2.2 s]
  NU-c [the cap 360987/500000 ↦ 7/8 (SPL-K's constant)]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-NU-d: accepted (want accepted) [2.5 s]
plant-NU-d: rejected (want recorded) [2.4 s]
    first error: plant-NU-d.lean:13:2: error: Type mismatch
witness-NU-d: accepted (want accepted) [2.2 s]
  NU-d [the cap only for τ ≥ 0 (negative τ dropped)]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-NU-e: accepted (want accepted) [2.5 s]
plant-NU-e: rejected (want recorded) [2.4 s]
    first error: plant-NU-e.lean:13:2: error: Type mismatch
witness-NU-e: accepted (want accepted) [2.3 s]
  NU-e [the odd kernel κ ↦ κ₊ (the definition by cases dropped)]: DETECTED (witness compiled: ¬ planted statement)
ok-NU-f: accepted (want accepted) [2.4 s]
plant-NU-f: rejected (want recorded) [2.5 s]
    first error: plant-NU-f.lean:14:2: error: Type mismatch
witness-NU-f: accepted (want accepted) [2.1 s]
  NU-f [the cap 360987/500000 ↦ 721973995/10⁹ (inside the window between the two rationals)]: NOT DETECTED (compiled characterisation of what a detection would have to refute; no refutation)
ok-NL-a: accepted (want accepted) [2.4 s]
plant-NL-a: rejected (want recorded) [2.3 s]
    first error: plant-NL-a.lean:13:70: error: Type mismatch
witness-NL-a: accepted (want accepted) [2.2 s]
  NL-a [the point 8123/5000 ↦ 0]: DETECTED (witness compiled: ¬ planted statement)
ok-NL-b: accepted (want accepted) [2.5 s]
plant-NL-b: rejected (want recorded) [2.2 s]
    first error: plant-NL-b.lean:13:70: error: Type mismatch
witness-NL-b: accepted (want accepted) [2.0 s]
  NL-b [the lower value 72197399/10⁸ ↦ 72197399/10⁷ (a digit dropped)]: DETECTED (witness compiled: ¬ planted statement)
ok-NL-c: accepted (want accepted) [2.1 s]
plant-NL-c: rejected (want recorded) [2.2 s]
    first error: plant-NL-c.lean:13:70: error: Type mismatch
witness-NL-c: accepted (want accepted) [2.2 s]
  NL-c [the lower value 72197399/10⁸ ↦ 72197401/10⁸ (above the cap)]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-NL-d: accepted (want accepted) [2.1 s]
plant-NL-d: rejected (want recorded) [2.6 s]
    first error: plant-NL-d.lean:14:70: error: Type mismatch
witness-NL-d: accepted (want accepted) [2.3 s]
  NL-d [the point 8123/5000 ↦ 13/8 (= 8125/5000, the point of the session-15 prototype)]: NOT DETECTED (compiled characterisation of what a detection would have to refute; no refutation)
ok-NL-e: accepted (want accepted) [2.5 s]
plant-NL-e: rejected (want recorded) [2.4 s]
    first error: plant-NL-e.lean:13:70: error: Type mismatch
witness-NL-e: accepted (want accepted) [2.2 s]
  NL-e [the strict inequality < ↦ ≤]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-NL-f: accepted (want accepted) [2.3 s]
plant-NL-f: rejected (want recorded) [2.3 s]
    first error: plant-NL-f.lean:14:70: error: Type mismatch
witness-NL-f: accepted (want accepted) [2.4 s]
  NL-f [the lower value 72197399/10⁸ ↦ 7219739995/10¹⁰ (inside the window between the two rationals)]: NOT DETECTED (compiled characterisation of what a detection would have to refute; no refutation)
ok-NK-a: accepted (want accepted) [2.7 s]
plant-NK-a: rejected (want recorded) [2.4 s]
    first error: plant-NK-a.lean:31:2: error: Type mismatch
witness-NK-a: accepted (want accepted) [2.3 s]
  NK-a [the constant 360987/500000 ↦ 7/10]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-NK-b: accepted (want accepted) [2.4 s]
plant-NK-b: rejected (want recorded) [2.5 s]
    first error: plant-NK-b.lean:23:2: error: linarith failed to find a contradiction
witness-NK-b: accepted (want accepted) [2.2 s]
  NK-b [the constant 360987/500000 ↦ 7/8 (SPL-K)]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-NK-c: accepted (want accepted) [2.5 s]
plant-NK-c: rejected (want recorded) [2.4 s]
    first error: plant-NK-c.lean:19:14: error: Function expected at
witness-NK-c: accepted (want accepted) [2.3 s]
  NK-c [the hypothesis 0 < λ dropped]: DETECTED (witness compiled: ¬ planted statement)
ok-NK-d: accepted (want accepted) [2.6 s]
plant-NK-d: rejected (want recorded) [2.4 s]
    first error: plant-NK-d.lean:31:2: error: Type mismatch
witness-NK-d: accepted (want accepted) [2.4 s]
  NK-d [the power λ^{−3/2} ↦ λ^{−1/2}]: DETECTED (witness compiled: ¬ planted statement)
ok-NK-e: accepted (want accepted) [2.7 s]
plant-NK-e: rejected (want recorded) [2.4 s]
    first error: plant-NK-e.lean:31:2: error: Type mismatch
witness-NK-e: accepted (want accepted) [2.3 s]
  NK-e [the power λ^{−3/2} ↦ λ^{−5/2}]: DETECTED (witness compiled: ¬ planted statement)
ok-NK-f: accepted (want accepted) [2.4 s]
plant-NK-f: rejected (want recorded) [2.2 s]
    first error: plant-NK-f.lean:22:47: error: Application type mismatch: The argument
witness-NK-f: accepted (want accepted) [2.2 s]
  NK-f [the norm ‖g‴‖₁ ↦ ‖g″‖₁]: DETECTED (witness compiled: ¬ planted statement)
ok-NK-g: accepted (want accepted) [2.4 s]
plant-NK-g: rejected (want recorded) [2.3 s]
    first error: plant-NK-g.lean:19:30: error: Application type mismatch: The argument
witness-NK-g: accepted (want accepted) [2.3 s]
  NK-g [the hypothesis SplAmplitude dropped]: DETECTED (witness compiled: ¬ planted statement)
ok-NK-h: accepted (want accepted) [2.5 s]
plant-NK-h: rejected (want recorded) [2.4 s]
    first error: plant-NK-h.lean:32:2: error: Type mismatch
witness-NK-h: accepted (want accepted) [2.4 s]
  NK-h [the constant 360987/500000 ↦ 360987/5000000 (a digit dropped)]: DETECTED (witness compiled: ¬ planted statement)
ok-NC-a: accepted (want accepted) [2.4 s]
plant-NC-a: rejected (want recorded) [2.6 s]
    first error: plant-NC-a.lean:18:17: error: Application type mismatch: The argument
witness-NC-a: accepted (want accepted) [2.1 s]
  NC-a [the range c ≤ 72197399/10⁸ ↦ c ≤ 7/8]: DETECTED (witness compiled: ¬ planted statement)
ok-NC-b: accepted (want accepted) [2.8 s]
plant-NC-b: rejected (want recorded) [2.5 s]
    first error: plant-NC-b.lean:19:17: error: Application type mismatch: The argument
witness-NC-b: accepted (want accepted) [2.3 s]
  NC-b [the range c ≤ 72197399/10⁸ ↦ c ≤ 360987/500000 (the cap)]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-NC-c: accepted (want accepted) [2.7 s]
plant-NC-c: rejected (want recorded) [3.0 s]
    first error: plant-NC-c.lean:18:17: error: Application type mismatch: The argument
witness-NC-c: accepted (want accepted) [2.2 s]
  NC-c [the range c ≤ 72197399/10⁸ ↦ c ≤ 72197/10⁵]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-NC-d: accepted (want accepted) [2.5 s]
plant-NC-d: rejected (want recorded) [2.6 s]
    first error: plant-NC-d.lean:20:2: error: Type mismatch
witness-NC-d: accepted (want accepted) [2.3 s]
  NC-d [the hypothesis 0 < λ dropped inside the negation]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
```

## Other files

- `names-and-axioms.lean.txt`, `names-and-axioms.out`: `#check` of every Mathlib name the sanity layer uses, at the
  pin, and `#print axioms` of all 46 sanity theorems (46 lines, each propext, Classical.choice, Quot.sound).
- `numerics/`: `kappa.py.txt` (60-digit decimal evaluation of `|κ|`, scan of `(0, 8]`), `window.py.txt` (argmax, the
  window, the super-level set, values at `τ = 10, 12, 16, 20`), `crosscheck.py.txt` (Simpson cross-check), and their
  outputs. Stdlib Python, run with `python3 -I`. Not an enclosure.

## File hashes (SHA-256)

```
7dd0da51b2d72e7e61b09c94a97b970b2e34edad0e51618e0a0f01f348939345  SUMMARY.txt
bb215f8b3aae5df55bdc547ff427e77131351de8893fe5187ff2197b1f7698d3  names-and-axioms.lean.txt
b1268d69d8ee7ec14fccefa3ba7887577426fcd7ac3d7477c919d7cc1381c5b2  names-and-axioms.out
0d2f0234ef63318082b1767f807e34412dacda722145c59f7322a8303e89235c  ok-NC-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NC-a.out
0d2f0234ef63318082b1767f807e34412dacda722145c59f7322a8303e89235c  ok-NC-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NC-b.out
0d2f0234ef63318082b1767f807e34412dacda722145c59f7322a8303e89235c  ok-NC-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NC-c.out
0d2f0234ef63318082b1767f807e34412dacda722145c59f7322a8303e89235c  ok-NC-d.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NC-d.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-a.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-b.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-c.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-d.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-d.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-e.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-e.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-f.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-f.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-g.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-g.out
af5e6cf9bcab9333f193a79af566fa37adfa829e34d7bdc2076a2953f2fe8383  ok-NK-h.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NK-h.out
d235b29bc89076e37b0a45b1b29b986367439ce3d361cf6b856124dcaaeb7cfc  ok-NL-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NL-a.out
d235b29bc89076e37b0a45b1b29b986367439ce3d361cf6b856124dcaaeb7cfc  ok-NL-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NL-b.out
d235b29bc89076e37b0a45b1b29b986367439ce3d361cf6b856124dcaaeb7cfc  ok-NL-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NL-c.out
d235b29bc89076e37b0a45b1b29b986367439ce3d361cf6b856124dcaaeb7cfc  ok-NL-d.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NL-d.out
d235b29bc89076e37b0a45b1b29b986367439ce3d361cf6b856124dcaaeb7cfc  ok-NL-e.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NL-e.out
d235b29bc89076e37b0a45b1b29b986367439ce3d361cf6b856124dcaaeb7cfc  ok-NL-f.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NL-f.out
4dec017c3c2c098f22ef648d1071f5089f5c2cdcbe1f6c6e0a6d4b6d7462b01e  ok-NU-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NU-a.out
4dec017c3c2c098f22ef648d1071f5089f5c2cdcbe1f6c6e0a6d4b6d7462b01e  ok-NU-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NU-b.out
4dec017c3c2c098f22ef648d1071f5089f5c2cdcbe1f6c6e0a6d4b6d7462b01e  ok-NU-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NU-c.out
4dec017c3c2c098f22ef648d1071f5089f5c2cdcbe1f6c6e0a6d4b6d7462b01e  ok-NU-d.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NU-d.out
4dec017c3c2c098f22ef648d1071f5089f5c2cdcbe1f6c6e0a6d4b6d7462b01e  ok-NU-e.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NU-e.out
4dec017c3c2c098f22ef648d1071f5089f5c2cdcbe1f6c6e0a6d4b6d7462b01e  ok-NU-f.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-NU-f.out
1e2d1fb59a6969fea585c5b3cda1884050563f75e2da0d047b19778904e7a13b  plant-NC-a.lean.txt
7d5ef6e373df66027498dc654e0da1f172bc860be3f2967ffe499b15771a06e2  plant-NC-a.out
89819e4248b01e1a6b26dd849bfee454b75fd27f470d98e168224fd7fa990cb4  plant-NC-b.lean.txt
5f0ac497e94ba5e4b056bca14ad245890cb9c39b47b493afccfb6f7cb1686aa7  plant-NC-b.out
a339ee4f7dec9e3deb372bd49cf47786e93c6a3a083f87ef69f58a17452bb1e2  plant-NC-c.lean.txt
b5abd971fe87f54dec86e4562863fa7522b7a4625c4503c1723385cc32b4362d  plant-NC-c.out
9dd7be1819bbdc9ed80c824723a05de49d119cd5daa12c8a3a5e6092087f373f  plant-NC-d.lean.txt
590b1ad5fd3898f95fc412e72c99a04d840e736d511bcb2392e44b472bf7b92c  plant-NC-d.out
f9cfdf180c8e13a07f92ecc70d92b0fe5382375d5e1827f033a51708219875b7  plant-NK-a.lean.txt
a5297949c9f58dc24288bc2086b1be8224eb27c6ee1b6227ca58094b993a1a48  plant-NK-a.out
b74d158078c75a5a2af3d2a01d03d6e131058d4b165d3b807b1b96cc43d87dfc  plant-NK-b.lean.txt
ae756d206532df04f5c0c0a9eea29fddfd9979481dc8e6e0a029feffcf81364f  plant-NK-b.out
6d07a8ffd2388a97f38fd14ab6c32a1ee880248bc9eeacfce8969044d54a1d67  plant-NK-c.lean.txt
68bfc7e434219ab32d7f734fb781db81d4d1a8d76378ed24f8850bf45406043d  plant-NK-c.out
ee1776213bd2d9632dccb065b41b15c1fc1fe45d9e40db894ecfaa642ebf4470  plant-NK-d.lean.txt
7106b50b42a31f18e8545086ed81189cbc7e685dba40131c45c6af10c4d17485  plant-NK-d.out
2b33cd2887e6ede1a59a254642e1004c522ed1f02110cea9303523b421b40eac  plant-NK-e.lean.txt
dc2733879d6f98d5f852976300b539a5db10bc5f93d595ea1aed1f3578682f1f  plant-NK-e.out
0172022eef7fc235e7416579ca7e4a864c71427e1d16d19de6ef5bf82a39c56f  plant-NK-f.lean.txt
173cec37142560b78da775f77d65d1ffcbc1e7e5f956a66d0117db7ae71e5010  plant-NK-f.out
2fc31e85e6a479b986a5d6e54b57ef01a2a80312590db74f6173ae29310994e6  plant-NK-g.lean.txt
231725474e99086023a4f30ceab94f1706caf6a3a84c038b8ee81085537c98c0  plant-NK-g.out
f3524422284718b2338d73d840949bfe0f2eade90ddfbdce3577cfd283e4d57c  plant-NK-h.lean.txt
91efd3c85d146c7fbb3c0a1a93d8acc99d0d9749a50c37cee3467a2df3e465bc  plant-NK-h.out
cc06d588b2b88b86f2c26064459951ad06c6b6f8442e4284b8424ff46f2fd0c1  plant-NL-a.lean.txt
676b588579fdff5c29085f8577d3550dd864333f24641823ddfc6c4b182cdc39  plant-NL-a.out
a6f9759dc537d3c2ca0b1d091c3fc1dc3ec49c5388ba88687ad8bd3bc35d99d5  plant-NL-b.lean.txt
67639ccc1d6ed74c81bbafb3ce4d3e55bd8125fab58865a4fe1270aa660b084a  plant-NL-b.out
e560cb2b0a6115f64af7202420ba443e727e634397475a59338bc7dc1cd8b7dc  plant-NL-c.lean.txt
b840bb9b8f13cc68a4303285ec3fb5d169ff33bebdc745a8d1851d9b963a4777  plant-NL-c.out
74a4d4c3fc4971bbc6ed5e762109f2084ddb37e190c3fc791d9c69298188a7b1  plant-NL-d.lean.txt
519659d4b2745f2f48ca92715d07ffb1febe744c938d483f54124e514618442d  plant-NL-d.out
a6900be6241dad80bb8c3485fdf87fd575d568c3fb899e648a5349827f201cd1  plant-NL-e.lean.txt
3b4d7a0ec305475aab162bc96f7fd4e3ea001e6685b6b45b99e01d32febcd587  plant-NL-e.out
524b84d920cde8f3dd3f36f11694c45ecd538bb8e5300a9e0de5db6756a58e36  plant-NL-f.lean.txt
54e1256759cb985e88b770eff94f15e1afa482237c1bb89b364bc00ef7e88672  plant-NL-f.out
059dc3d7d7f0e813719faf26e2562095f1b4c22bb1ea7b358512e9e10cac6e7c  plant-NU-a.lean.txt
9574b27bba4f4429ce40ac8d82294b94e8bf30adc1d7995fc9a2db8899c501ea  plant-NU-a.out
2e5c44e3250f556af7c528a818158a6695fc09a4a179ee7a08b69bb712d5ec9d  plant-NU-b.lean.txt
c807ee379189011495b8eba8240d2999bd3d26fafdd0be98a23b23d511db7038  plant-NU-b.out
fcbc59a6685bc122379398476dbac96f2aae0653672664166ed3be974b06f997  plant-NU-c.lean.txt
e9f8b1f1f6a4e8f231a64fddd23bc54d25ece09f39c29d68898f6aebd5ea56e9  plant-NU-c.out
09eb0d41dabd0592be94a2073ee1cd9aa871e9d5bda7982ac3e61eeb3686033c  plant-NU-d.lean.txt
b7b3d2f787e9b48d2526374bb69fd43fe670837ea8400ac6c4cd583c7b1ef8e6  plant-NU-d.out
5529f4e3a617899ca73403f59d6d5862d260263bc6f95a4a63b58ad13b48e8d2  plant-NU-e.lean.txt
55ebdd15ad168c020b5f3309714c90094d83f92171b5e35d9775121978424cb4  plant-NU-e.out
20af3acb49e09c601e28ad68d81b41203c2e777a517681ebf510389e39f2b02c  plant-NU-f.lean.txt
de4422ef7109944d46daa7e2d80781506c49d86716296571202c5239863b6da9  plant-NU-f.out
81f1bc7a5edf0b994da9de48da41493943ad7d8c80a4dc0b83f22f09de4afc14  plants_spln.py.txt
db874b982fcfbf7e3bfe770f55aa65c745a75e0a1635e3a824785cf044b703ef  witness-NC-a.lean.txt
750e0d7ee6430448125b42744f351e83ea86246b681866c2126e3b09253d2d88  witness-NC-a.out
5d9312ff186b52b41494d5edffd6fc1c60ca1d20a5b7767e7b0f16cbe07c013e  witness-NC-b.lean.txt
a7eda3b210ab955654a03807d1f29854ebc7a6d4ab260eba0ec7eac13da59b6d  witness-NC-b.out
cfc8328fff988649abb9ee04fbee1d8d39eb5676a8bbdae20874f5054d13bd21  witness-NC-c.lean.txt
ecc3b695f99703ae0fb2e5cfa30fd918d6b1139b16ceb41c837486f177cdf149  witness-NC-c.out
15b022d20196498992ca6ca277836f1bd87eeb1bc23dedb6ea79725cc1cf4110  witness-NC-d.lean.txt
7dffcaddab4888c2419bd4935cbebbc564a6c4c64600ad50fb9a357b685fe146  witness-NC-d.out
23f276218759afa59610b690485f8752d8d9c5b725b7c3e5c2228eead1c82491  witness-NK-a.lean.txt
a268287d4cc87d012c9c31113802d8495584396c861fa88747306cf7438d3d32  witness-NK-a.out
bf9719610c791c37d07475d4610aaa589516af4dca7c1182b5d93074d9c4ffd3  witness-NK-b.lean.txt
61c9a26cc77e8a1f7158c428a9bfb4a3ead674623840e4d312faac5e3762fc40  witness-NK-b.out
32bdbde3e74efa757dcb0e187e1b90afadc0fb8897eb7e24a1a54f5e582cec8c  witness-NK-c.lean.txt
fb95119e56a06dff5885030173582b4adf23a37d6a86388f034fce2f2a74cb6f  witness-NK-c.out
2ac42ec039a1b2c81d12dbfa50ff40c37f1f0c562582b45ffd952c7de197fd16  witness-NK-d.lean.txt
47fbe7e9eb405f13d1be4d6a8f6f050cd4c4e91e1a026b1141c3595f17d46f25  witness-NK-d.out
9bd63d4ccdaa04e651c8d093568d10dbc8fb15366faa8ecaf5ef900dea9b8efb  witness-NK-e.lean.txt
d07b1f2df7b3b4b0663aea8211ed99b27d6776d7607758875e950c2e0764102b  witness-NK-e.out
be36debb56ff76cf610080f86b72037414b63db8a5df5a3396f88cd06eb0ea6a  witness-NK-f.lean.txt
161bc3ae30fcf4e44abcaa68ee0d953256f725cf4b42298e21745942d19ec164  witness-NK-f.out
6f7286233227acebb721e04e2427a6f380722a4cdca2d19ad9563830d6c5429e  witness-NK-g.lean.txt
1f12a2213cdb3fa7b320d6cd22629e36372c8ffeddb39fd0143ab83b635a096f  witness-NK-g.out
7f8b4439610c6662cf7ae637f75e4ca4c224a353a0a327cbacde372a77cf27e5  witness-NK-h.lean.txt
977ac37d14c32e69925ebeb45a1a9b3084b5d08fce92d48d8b8ffb620663b689  witness-NK-h.out
85cdc49982ed101a97374e6ad5189287677b11d4817688c537f728bc359ddb63  witness-NL-a.lean.txt
15419ec23db8f9bb68fcb62ec9624bfdc17170bf189ced39b3ad66d3f8485302  witness-NL-a.out
cff5d443f75dbd304ac9a88abcc37f14615b7b24c037fe8c5a5b05cc72e77a84  witness-NL-b.lean.txt
3ee7a7bcd46fda2a069d6dce19ce419d9d4bce077e2348595559a32cdc9d1f0e  witness-NL-b.out
b4093c6677e5a6b2db650d9609ab9ba04a518d817959fbef09270656e93429fe  witness-NL-c.lean.txt
2373cd14784030558824eec281cda302734c7ce42e7c836e465e9967e00b8aad  witness-NL-c.out
09fb5a2a56d09ae322535c01b71d9081609ee6d0f0e0d3cbe59f2a68646943fe  witness-NL-d.lean.txt
9878c77151c594d2ce06ff318486f67ac010934d386a086e719d8c806ac449b9  witness-NL-d.out
e1bf88e3422a77c1b529d34677ca8a4ae29ea933a423da1535ee86d9ae192426  witness-NL-e.lean.txt
bda7b3fc97466a9a8755b5b7c7fee11bdf00990a02b314039e6fd8e3a1f3d1d5  witness-NL-e.out
2d63fcea80af65c947b2c8ec8f63cfb83af7b30cf5e6e55ab80a6186c8cd9fd2  witness-NL-f.lean.txt
89c96f0ddab093b5a77d7402d5b7a0c6a55f2c0edf5d0bb139f820145a9dc5ae  witness-NL-f.out
3ee1efdbb28562c6dd5c4e3c510380d7e60ee15677b8d1536bd86f3e8d2d15da  witness-NU-a.lean.txt
4ab5d32aa0ee42aeae182892e9686f9f1f8bc641609b00aeb66bd859102fb72c  witness-NU-a.out
d6a87269eec3dbe0d907d9b1127277f05cb47acaa33a28200c5752817b247a91  witness-NU-b.lean.txt
026fb1493db1caa183325953c092bf4acf8a9e98bf0d734476a415ce714a552f  witness-NU-b.out
3fdde124d4a92b27169fef8ff43abc7e553d3082165f7f8c30807bdde03b4039  witness-NU-c.lean.txt
e8b66e5289b39e8ba043b8b156a458f1556471f61e96b2407d1f695ffb786886  witness-NU-c.out
de76a7d445787ddcaedaaded9ed57fb07e98a61a05f77d602af18d8108b0b24f  witness-NU-d.lean.txt
2f641a25f621a5c20329465caab4003ce6815cc7c50d3be2639f4293a734d34f  witness-NU-d.out
8c7a44022d451ff6be67a3104b505a3cca40165dcdef3a70893d4f0c9914918f  witness-NU-e.lean.txt
47795220caeb18f32e967f8b4b4e81f6a306c20ae9861d182f60b6958cc36c93  witness-NU-e.out
0f69ccc82fb1ddf28c5b15c1a49ef46730f6a2088205787afc3fe3c527cf8afe  witness-NU-f.lean.txt
bc4b71b304fc7b5cd19b8606853ca00ef1c43adac67816c30229c39d8504ca12  witness-NU-f.out
7e7ff5ceab4e654ba676cc0057a5f25fd503239eb138d9e10aa3606bd691c372  numerics/crosscheck.out
732c6e97429859143cb1f2d95414076b1aaf505360487fcb252edcb4ae422f38  numerics/crosscheck.py.txt
ed5db70d4e926616232b9e033772c1d1eeebe0a6fa9db4287e72dc9fcd372fc0  numerics/kappa.out
45f7d1054e2a4db31a3bf08c5c6cabc2dd0e35c7b461efa385bc850315be2643  numerics/kappa.py.txt
c29bd132686afa9465f7ddcb6305c7c185367a3f869c874b1d49b4bdf0df1a7d  numerics/window.out
e64cbdc478ee05ef0f0eed4c85a94c554172b9bd31df497255237b6c4089bc3c  numerics/window.py.txt
```
