# Batch LOC2: planted controls of the sanity layer (docs/lessons.md, rules 8 and 9)

Written by the A5U/LOC2 sanity agent on 2026-11-28 (generator run 2026-11-28T13:24:53Z to 2026-11-28T13:27:13Z UTC,
generator exit code 0) against the draft statement text, unchanged:

- `OscInt/Statements/TorusLocalizationC2.lean`, SHA-256 9310e8752e8cbe889385c32360cf5369fb151451bfb8e26a0bcaafb85a33a613
  (identical to the copy `stmt/TorusLocalizationC2.lean` from which the generator reads the statement text; the module
  itself is the repository's built `.olean`). Repository HEAD not recorded (the brief forbids every git command).
- Sanity layer `src/OscInt/Front/TorusLocalizationC2Sanity.lean` (module `OscInt.Front.TorusLocalizationC2Sanity`,
  namespace `OscInt.API.TorusLocalizationC2Sanity`), SHA-256 03146e86d24315d4f33ff57bdb7def3aade6e127251fe49c5b903e4c60b3b3e7.
- Generator `plants_loc2.py.txt` (= `gen/plants_loc2.py`), SHA-256 3582eeb539f5e4beed5d56086e01ec0010ea044694f4ebf773a54cf5771c221d.
- The lead's compiled K2 F-a witness, read-only copy `gen/witness-F-a-compiled.lean.txt`, SHA-256
  057c3a24e24dc0eb707f9c5606dce5ce2d2e1613a05fb8f9d1673c1f0cbe8124, identical to the repository's
  `docs/replay/plants/2026-11-28-K2-F-a-witness/witness-F-a-compiled.lean.txt`. The witness of L-a contains its
  namespace `OscInt.FaWitnessAux` verbatim, from the line after its import to `end OscInt.FaWitnessAux`, and uses its
  theorem `refute`.
- Used as data: `OscInt/Front/TriangularDecaySanity.lean` (SHA-256 88b88872…8ede) and the proved K2 theorems of
  `OscInt/Front/TriangularDecayFinal.lean` (SHA-256 1ed34f43…9c09), both as the repository's built modules.

Harness: as `plants-a5u/README.md` (scratch `lib/` mirror first on `LEAN_PATH`, sanity module compiled with
`--root=src -o lib/...olean`, `bin/leanrun nice -n 10 lake env … lean -DautoImplicit=false`, Lean 4.35.0, Mathlib
56a005855ea1, one Lean process at a time; times in `SUMMARY.txt` include waiting for other agents' Lean jobs).
Nothing in the repository was written.

Method: as batch K2. Copies: the statement constant, and for a plant in a definition also that definition and every
definition between it and the statement (`boxL2`/`boxLaplacian` → `locConstC2` → statement). Kinds: `not` DETECTED;
`relp` (K2-U → ¬ planted, compiled, and ¬ planted from the proved `OscInt.API.triDecayUpper`) DETECTED via the proved
K2-U; `weak` TRUE WEAKENING; `str` (planted → draft compiled: a strengthening) NOT DETECTED; `char` (the planted
definition differs from the draft's on a datum, compiled) NOT DETECTED. No file proves, or uses a proof of, K2-FQ.

## Outcome

11 plants: 4 DETECTED (L-a, L-b, L-d unconditionally; L-h via the proved K2-U, with the relative witness compiled
too), 1 TRUE WEAKENING (L-g), 6 NOT DETECTED (L-c, L-e, L-i, L-j, L-k: compiled planted → draft; L-f: compiled
characterisation). All 11 unplanted copies compile; all 11 planted copies are rejected by the copied scripts
(script-only, not counted).

| plant | mutation | outcome | evidence |
|---|---|---|---|
| L-a | support condition dropped | DETECTED | `χ = 1` (`C²`, `locConstC2 1 = 6`), `t = 1`, `p = (1/2, 0)`: `OscInt.FaWitnessAux.refute (locConstC2 1)` gives a continuous biperiodic phase and valid `B` with `locConstC2 1 · B < ‖∫ e^{i(Ψ + k₁/2)}‖` |
| L-b | factor `4` ↦ `0` | DETECTED | `χ₁`, zero phase, `t = 0`, `B = (2π)²`: the plant claims `‖∫ χ₁‖ ≤ 0`, `∫ χ₁ ≠ 0` |
| L-c | `ContDiff ℝ 2` ↦ `ContDiff ℝ 1` | NOT DETECTED | planted → draft compiled; no `C¹` counterexample built (`boxLaplacian` of a non-`C²` function is a junk value) |
| L-d | coefficient hypothesis on all `n` ↦ on `n ≠ 0` | DETECTED | zero phase, `t = 0`: `B = 0` is valid, the plant claims `‖∫ χ₁‖ ≤ 0` |
| L-e | coefficient `3/2` of `‖χ‖` ↦ `0` | NOT DETECTED | planted → draft compiled; undecided (Poincaré suggests it may be true) |
| L-f | Laplacian `∂₁² + ∂₂²` ↦ `2∂₁²` | NOT DETECTED | compiled: on `q = k₁² + 3k₂²` the planted Laplacian at `0` is `4`, the draft's `8`; undecided |
| L-g | normalisation `(2π)^{−2}` of `boxL2` dropped | TRUE WEAKENING | draft → plant compiled (unnormalised norm is `2π` times the normalised one) |
| L-h | `t` dropped from the lattice coefficients | DETECTED (via K2-U) | phase `s · triPhase 0`, `t = 0`: coefficients `triKernel 0 s n ≤ C s^{−2/3}`, the plant claims `‖∫ χ₁‖ ≤ locConstC2 χ₁ · C s^{−2/3}` for all `s ≥ 1` |
| L-i | factor `4` ↦ `1/8` | NOT DETECTED | planted → draft compiled; false on paper: zero phase with `χ ≈ cos²(k₁/2) cos²(k₂/2)` (in `H²₀`, approximable by admissible cutoffs) has `∫ χ = π² ≈ 9.87` against `(1/8)·1.349·4π² ≈ 6.66` (floating point) |
| L-j | hypothesis `Continuous Ψ` dropped | NOT DETECTED | planted → draft compiled; false on paper through the Bochner junk value: `Ψ = 0` near `supp χ₁`, `Ψ = π·1_V` with `V` non-measurable elsewhere makes every coefficient integral `0` (`B = 0`) while `∫ χ₁ ≠ 0`; not built (needs a non-measurable set) |
| L-k | periodicity of `Ψ` in `k₁` dropped | NOT DETECTED | planted → draft compiled; true on paper (the route expands `χ e^{iθ·k}` on the box and never uses periodicity) |

## Generator log (SUMMARY.txt)

See `SUMMARY.txt` (verbatim generator log, ending with the run times).

## File hashes (SHA-256)

See `SHA256SUMS.txt` in this directory (written after the run by `sha256sum`).
