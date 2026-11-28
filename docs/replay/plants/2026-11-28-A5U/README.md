# Batch A5U: planted controls of the sanity layer (docs/lessons.md, rules 8 and 9)

Written by the A5U/LOC2 sanity agent on 2026-11-28 (generator run 2026-11-28T13:14:42Z to 2026-11-28T13:24:53Z UTC,
generator exit code 0) against the draft statement text, unchanged:

- `OscInt/Statements/TriangularCrossover.lean`, SHA-256 0b7f8c315ac531cf9507132db09e6bb61f2416363e3fd766469f2ae5015b60bf
  (identical to the copy `stmt/TriangularCrossover.lean` from which the generator reads the statement text; the module
  itself is the repository's built `.olean`). Repository HEAD not recorded (the brief forbids every git command).
- Sanity layer `src/OscInt/Front/TriangularCrossoverSanity.lean` (module `OscInt.Front.TriangularCrossoverSanity`,
  namespace `OscInt.API.TriangularCrossoverSanity`), SHA-256 9332d30c3a047492fdc1843f69673f8d33bc437f49f7b3d039b304bab8058ae0.
- Generator `plants_a5u.py.txt` (= `gen/plants_a5u.py`), SHA-256 5b5154ccf5c8a1e5a37bdfe89eebc182d4727feb189a74b5db3f7896d824464f.
- Used as data: `OscInt/Front/TriangularDecaySanity.lean` (SHA-256 88b88872…8ede) and the proved K2 theorems of
  `OscInt/Front/TriangularDecayFinal.lean` (SHA-256 1ed34f43…9c09), both as the repository's built modules.

Harness: `.lake/build/lib/lean/OscInt` mirrored (symlinked files, real directories) into `lib/`, placed first on
`LEAN_PATH` before the repository's `lake env` path; the sanity module compiled with `--root=src -o lib/...olean`.
Every compile ran through `lean.sh` = `bin/leanrun nice -n 10 lake env bash -c 'LEAN_PATH=<scratch>/lib:$LEAN_PATH exec
lean -DautoImplicit=false …'` from `/home/user/lean-oscillatory` (Lean 4.35.0, Mathlib 56a005855ea1). One Lean process
at a time from this agent; `leanrun` serialises with other agents' Lean jobs, so the per-file times in `SUMMARY.txt`
include waiting. Nothing in the repository was written.

Method (as batch K2). For each plant: `ok-` = unplanted copy `P_TriCrossoverUpperStatement` (and `P_crossEnvelope` for
the plants in the envelope's definition) followed by copies (renamed `P_`) of every sanity declaration whose text
names a copied constant or an earlier copied declaration; must compile. `plant-` = the same with ONE textual mutation;
its rejection by the copied scripts is recorded and is never counted as a detection. `witness-` = the planted copy and
compiled theorem(s), with `#print axioms` (one line per theorem, only propext, Classical.choice, Quot.sound, checked by
the generator). Kinds: `not` (¬ planted, from unconditional data) DETECTED; `relp` (K2-D → ¬ planted, compiled, and
¬ planted from the proved `OscInt.API.triDecayLower`, compiled) DETECTED via the proved K2-D; `weak` (draft →
planted) TRUE WEAKENING. No file proves, or uses a proof of, A5U.

## Outcome

13 plants: 8 DETECTED (1 unconditionally from the sanity data: A-d; 7 via the proved K2-D, each with its relative
witness compiled too: A-a, A-b, A-c, A-m, A-g, A-i, A-j), 5 TRUE WEAKENINGS (A-e, A-f, A-h, A-k, A-l), none NOT
DETECTED. All 13 unplanted copies compile; all 13 planted copies are rejected by the copied scripts (script-only, not
counted).

| plant | mutation | outcome | evidence |
|---|---|---|---|
| A-a | envelope `s^{−1/4}` ↦ `s^{−1/3}` (in `crossEnvelope`) | DETECTED (via K2-D) | `α = a* + δ`, `0 < δ ≤ min(r, a*)/2`, `triRate α = 3/4`; for `t > δ^{−3}` the plant gives `C δ^{−1/3} t^{−7/9}` |
| A-b | window `\|α − a₀\| ≤ r` ↦ `≤ 1` | DETECTED (via K2-D) | the window contains `α = 0` (`triRate 0 = 2/3`); the bound gives `C a*^{−1/4} t^{−3/4}` |
| A-c | `t^{−2/3}` ↦ `t^{−3/4}` | DETECTED (via K2-D) | centre `α = a₀ = a*`, envelope `1`: `C t^{−3/4}` against `c t^{−2/3}` |
| A-m | whole bound ↦ `C t^{−3/4}` | DETECTED (via K2-D) | as A-c |
| A-d | hypothesis `1 ≤ t` dropped | DETECTED | `a5u_time_zero_bite`: at `t = 0` the right side is `0`, `‖triKernel a* 0 (0, 0)‖ = (2π)²` |
| A-e | `\|a₀\| = a*` ↦ `a₀ = a*` | TRUE WEAKENING | draft → plant (the centre `−a*` is dropped) |
| A-f | `∃ r > 0` ↦ `∃ r ≥ 0` | TRUE WEAKENING | draft → plant; also K2-U → plant (`r = 0`) and the plant from the proved K2-U: A5U's content is entirely in `r > 0` |
| A-g | crossover scale `t^{1/3}` ↦ `t^{1/2}` | DETECTED (via K2-D) | `α = a* + δ`: `C δ^{−1/4} t^{−19/24}` against `c t^{−3/4}` |
| A-h | crossover scale `t^{1/3}` ↦ `t^{1/4}` | TRUE WEAKENING | draft → plant (`E` antitone, `t ≥ 1`) |
| A-i | plateau value `1` ↦ `0` (in `crossEnvelope`) | DETECTED (via K2-D) | centre: the plant claims `‖triKernel a* t n‖ ≤ 0` |
| A-j | envelope argument `\|α − a₀\|` ↦ `\|α\|` | DETECTED (via K2-D) | centre: argument `a* t^{1/3}`, bound `C a*^{−1/4} t^{−3/4}` against `c t^{−2/3}` |
| A-k | envelope `s^{−1/4}` ↦ `s^{−1/5}` | TRUE WEAKENING | draft → plant (`s^{−1/4} ≤ s^{−1/5}` for `s > 1`) |
| A-l | envelope factor dropped | TRUE WEAKENING | draft → plant (`E ≤ 1`, `C ≥ 0`) |

Why the rate and exponent plants need K2-D: refuting a faster rate needs a lower bound of `triKernel` at large `t`,
which is K2-D's content; K2-D is proved (`OscInt.API.triDecayLower`), so these count as DETECTED, and each witness
file also contains the relative form. The weakenings A-k, A-h and A-l show that the envelope exponent `−1/4` and the
scale `1/3` are the strongest choices compatible with K2-D, not the only compatible ones (see the report, finding 1).

## Generator log (SUMMARY.txt)

See `SUMMARY.txt` (verbatim generator log, ending with the run times).

## File hashes (SHA-256)

See `SHA256SUMS.txt` in this directory (written after the run by `sha256sum`).
