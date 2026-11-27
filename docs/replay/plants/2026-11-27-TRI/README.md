# Batch TRI: planted controls of the sanity layer (docs/lessons.md, rules 8 and 9)

Written by the sanity-layer agent of the lead on 2026-11-27 (run 2026-11-27T00:43Z to 00:45Z UTC, generator exit
code 0) against the draft statement text, unchanged:

- `OscInt/Statements/TriangularAniso.lean` at repository HEAD 9a960c5e2df6daece52e1349ddcae8ddaf75ebaa, SHA-256
  8e5ae6516c52fa804d5c45939541a0de45bb5d1d4dfbeff6279d03c516b4a0a7 (identical to `TriangularAniso.statement.lean` of
  the brief and to the copy `src/OscInt/Statements/TriangularAniso.lean` compiled here).
- Sanity layer `TriangularAnisoSanity.lean` (= `src/OscInt/Front/TriangularAnisoSanity.lean`, module
  `OscInt.Front.TriangularAnisoSanity`, namespace `OscInt.API.TriangularAnisoSanity`), SHA-256
  b5f206352d8f2dff0b7f4790e18e1b3a1263a21be6caf262aa288147706354f9.
- Generator `plants_tri.py.txt` (= `gen/plants_tri.py`), SHA-256
  150213c714e738eaed296adda38f1c8949fd5ebbd2c01ba91ba14b93952dbfa7.

Harness: the scratch-library harness of `docs/HANDOFF.md` (`.lake/build/lib/lean/OscInt` mirrored into `lib/`, placed
first on `LEAN_PATH`; statement and sanity modules compiled with `--root=src -o lib/...olean`; Lean 4.35.0, Mathlib
pin 56a005855ea1). Each generated file imports `OscInt.Front.TriangularAnisoSanity` only. One Lean process at a time.
Nothing in the repository was written.

Method (as batch SPL). For each plant: `ok-` = unplanted copy `P_<Statement>` followed by copies (renamed `P_`) of
every sanity theorem that takes that statement constant as a hypothesis; must compile. `plant-` = the same with ONE
textual mutation; its rejection by the copied scripts is recorded and is never counted as a detection. `witness-` =
the planted copy and compiled theorem(s), with `#print axioms` (only propext, Classical.choice, Quot.sound, checked
by the generator). Kinds: `not` (¬ planted, from unconditional data) DETECTED; `rel` (true statement → ¬ planted)
DETECTED RELATIVE TO THE TRUE STATEMENT; `weak` (draft → planted) TRUE WEAKENING; `char` NOT DETECTED, with a
compiled characterisation of what a detection would need. No file proves, or uses a proof of, a batch-TRI statement.

## Outcome

10 plants: 6 DETECTED (TRI-Q-a, TRI-Q-b, TRI-Q-c, TRI-W-b, TRI-K-a, TRI-K-b), 2 DETECTED RELATIVE TO THE TRUE
STATEMENT and NOT DETECTED unconditionally (TRI-X-a, TRI-X-b), 1 TRUE WEAKENING (TRI-X-c), 1 NOT DETECTED (TRI-W-a).
All 10 unplanted copies compile; all 10 planted copies are rejected by the copied scripts (script-only, not
counted, including the weakening TRI-X-c).

| plant | statement | mutation | outcome | evidence |
|---|---|---|---|---|
| TRI-Q-a | TRI-Q | `= -12` ↦ `= 12` | DETECTED | `quarter_halfPi_quartic`: exact value `−12` at `α = 1/4`, `(π/2, π/2)` |
| TRI-Q-b | TRI-Q | `12(8α² − 1)` ↦ `12(8α² + 1)` | DETECTED | `quarter_theta`: exact value `−6` at `α = 1/4`, `(θ, −θ)` (plant: 18) |
| TRI-Q-c | TRI-Q | `\|α\| ≤ 1/2` ↦ `\|α\| ≤ 1` | DETECTED | at `α = 1`, `arccos(−2) = π`; `D²[(1, 1), (1, 0)] = −1 ≠ 0` at `(π, −π)` |
| TRI-X-a | TRI-X | `\|α\| = a*` ↦ `\|α\| = 1/2` | REL. / NOT DET. uncond. | TRI-W → ¬plant; TRI-K → ¬plant (via `kA5_not_foldOrNondeg`, `kA5_not_isA3`) |
| TRI-X-b | TRI-X | `arccos(−2α)` ↦ `arccos(2α)` (4×) | REL. / NOT DET. uncond. | TRI-W → ¬plant (`4j = 1` or `2j = 1` in ℤ) |
| TRI-X-c | TRI-X | conclusion `\|α\| = a* ∧` dropped | TRUE WEAKENING | draft → plant, compiled |
| TRI-W-a | TRI-W | `−60√2` ↦ `60√2` | NOT DETECTED | compiled: draft ∧ plant → no reduced curve at `(3π/4, −3π/4)`; none constructed |
| TRI-W-b | TRI-W | second point `(−θ, θ)` ↦ `(θ, θ)` | DETECTED | `kDiag_not_isA5`: Hessian `(√2/2)·I` at `(3π/4, 3π/4)` |
| TRI-K-a | TRI-K | `∨ IsA5Point` dropped | DETECTED | `kA5_not_foldOrNondeg`, `kA5_not_isA3` at `α = a*` |
| TRI-K-b | TRI-K | hypothesis `α ≠ 0` dropped | DETECTED | `zero_halfPi_none`: Hessian zero at `α = 0`, `(π/2, π/2)` |

Why TRI-W-a and the unconditional TRI-X plants are not detected: an unconditional witness needs an A5 point
(`IsA5Point` asks for a globally smooth reduced curve and its reduced derivatives to order 6), or, for the sextic, a
reduced curve for `v = (1, 1)`, `w = (1, −1)` with its sixth derivative. Locally the curve is
`h(u) = π/4 − arcsin(1/(√2 cos u))` (θ = 3π/4), which must be extended to a smooth function on ℝ (cut-off), and its
sixth derivative computed; not attempted within the time box. A SymPy check run by this agent, not a Lean artefact (series of the reduced
function from the phase) gives `0, 0, 0, 0, 0, ∓60√2` at `±a*`, confirming the draft value, not the plant.

## Generator log (SUMMARY.txt)

```
ok-TRI-Q-a: accepted (want accepted) [4.4 s]
plant-TRI-Q-a: rejected (want recorded) [4.2 s]
    first error: plant-TRI-Q-a.lean:39:10: error: Application type mismatch: The argument
witness-TRI-Q-a: accepted (want accepted) [3.7 s]
  TRI-Q-a [the value −12 at (π/2, π/2) ↦ 12]: DETECTED (witness compiled: ¬ planted statement)
ok-TRI-Q-b: accepted (want accepted) [3.9 s]
plant-TRI-Q-b: rejected (want recorded) [4.7 s]
    first error: plant-TRI-Q-b.lean:35:49: error: unsolved goals
witness-TRI-Q-b: accepted (want accepted) [4.6 s]
  TRI-Q-b [12(8α² − 1) ↦ 12(8α² + 1)]: DETECTED (witness compiled: ¬ planted statement)
ok-TRI-Q-c: accepted (want accepted) [4.4 s]
plant-TRI-Q-c: rejected (want recorded) [4.8 s]
    first error: plant-TRI-Q-c.lean:65:44: error: Type mismatch
witness-TRI-Q-c: accepted (want accepted) [4.1 s]
  TRI-Q-c [the range |α| ≤ 1/2 ↦ |α| ≤ 1]: DETECTED (witness compiled: ¬ planted statement)
ok-TRI-X-a: accepted (want accepted) [4.6 s]
plant-TRI-X-a: rejected (want recorded) [4.4 s]
    first error: plant-TRI-X-a.lean:21:20: error: Application type mismatch: The argument
witness-TRI-X-a: accepted (want accepted) [4.3 s]
  TRI-X-a [the exceptional value a* ↦ 1/2]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-TRI-X-b: accepted (want accepted) [4.1 s]
plant-TRI-X-b: rejected (want recorded) [4.0 s]
    first error: plant-TRI-X-b.lean:58:2: error: Type mismatch
witness-TRI-X-b: accepted (want accepted) [5.1 s]
  TRI-X-b [θ = arccos(−2α) ↦ arccos(2α)]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-TRI-X-c: accepted (want accepted) [3.8 s]
plant-TRI-X-c: rejected (want recorded) [4.7 s]
    first error: plant-TRI-X-c.lean:18:10: error(lean.projNonPropFromProp): Invalid projection: Cannot project a value of non-propositional type
witness-TRI-X-c: accepted (want accepted) [4.8 s]
  TRI-X-c [the conclusion |α| = a* dropped]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-TRI-W-a: accepted (want accepted) [3.9 s]
plant-TRI-W-a: rejected (want recorded) [3.8 s]
    first error: plant-TRI-W-a.lean:41:2: error: Type mismatch: After simplification, term
witness-TRI-W-a: accepted (want accepted) [3.9 s]
  TRI-W-a [the sign of −60√2 flipped]: NOT DETECTED (compiled: draft ∧ plant → no reduced curve exists; a detection needs a reduced curve with its sixth derivative, not constructed)
ok-TRI-W-b: accepted (want accepted) [3.8 s]
plant-TRI-W-b: rejected (want recorded) [4.4 s]
    first error: plant-TRI-W-b.lean:24:17: error: Application type mismatch: The argument
witness-TRI-W-b: accepted (want accepted) [3.8 s]
  TRI-W-b [the second point (−θ, θ) ↦ (θ, θ)]: DETECTED (witness compiled: ¬ planted statement)
ok-TRI-K-a: accepted (want accepted) [4.0 s]
plant-TRI-K-a: rejected (want recorded) [3.8 s]
    first error: plant-TRI-K-a.lean:19:24: error: Application type mismatch: The argument
witness-TRI-K-a: accepted (want accepted) [3.8 s]
  TRI-K-a [the A5 alternative dropped]: DETECTED (witness compiled: ¬ planted statement)
ok-TRI-K-b: accepted (want accepted) [4.6 s]
plant-TRI-K-b: rejected (want recorded) [4.5 s]
    first error: plant-TRI-K-b.lean:19:3: error: Function expected at
witness-TRI-K-b: accepted (want accepted) [4.5 s]
  TRI-K-b [the hypothesis α ≠ 0 dropped]: DETECTED (witness compiled: ¬ planted statement)
```

## File hashes (SHA-256)

```
468f63588d0553440103801ad9bfe3034fba8a5ad69667f0b15d2fddd452b351  SUMMARY.txt
6be3e8e32136d55a780560ed3339c417d4d2dda3de185d1ece272b7e8fc8f2dc  ok-TRI-K-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-K-a.out
6be3e8e32136d55a780560ed3339c417d4d2dda3de185d1ece272b7e8fc8f2dc  ok-TRI-K-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-K-b.out
5ec81da0764eeb56a2ba725f760e8c2f9d8b09ffdfa66110f3ac4204103b56e1  ok-TRI-Q-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-Q-a.out
5ec81da0764eeb56a2ba725f760e8c2f9d8b09ffdfa66110f3ac4204103b56e1  ok-TRI-Q-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-Q-b.out
5ec81da0764eeb56a2ba725f760e8c2f9d8b09ffdfa66110f3ac4204103b56e1  ok-TRI-Q-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-Q-c.out
1908e6b4a4db03d7221d8d164c3d7f925c3bb0c3e20b84b7b686e8dba3dbe53d  ok-TRI-W-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-W-a.out
1908e6b4a4db03d7221d8d164c3d7f925c3bb0c3e20b84b7b686e8dba3dbe53d  ok-TRI-W-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-W-b.out
1039ac96ff84565911bbf0c7348fe4545b7cf29523a9a78123f5f9e595b0fa81  ok-TRI-X-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-X-a.out
1039ac96ff84565911bbf0c7348fe4545b7cf29523a9a78123f5f9e595b0fa81  ok-TRI-X-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-X-b.out
1039ac96ff84565911bbf0c7348fe4545b7cf29523a9a78123f5f9e595b0fa81  ok-TRI-X-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-TRI-X-c.out
aef47129254afe3cb836d8aef643db049cf56fef1914d2c381391e3d5bece80e  plant-TRI-K-a.lean.txt
80a84d8dab31762d00b7ec0389424acf451d94926f63a79cdab4ad4b7d3aad71  plant-TRI-K-a.out
62279f215b512559cbc73c701941a56819dd9935d0cc4f80f2d88b10d8a55826  plant-TRI-K-b.lean.txt
db1f95324e0f334760e130627515c5b936d491acc2d8566fffd8ac264a61552f  plant-TRI-K-b.out
627174a331ece1523e09e48e11fc7c119707708afaebceb42a0943a75471fb3e  plant-TRI-Q-a.lean.txt
d665f2519d4d970e9330f59b277e55523bc3f97575fd991d611de6b12a4e88b1  plant-TRI-Q-a.out
0dc7a7fd4754ccc4ceaeeac1d4a33b0121daf78e00c20569ade2c757fed9e097  plant-TRI-Q-b.lean.txt
3ad779aafff4e6534613ea325c2437d4f379a1546787409139b7a690b338a9c7  plant-TRI-Q-b.out
8aa5153feb35819d1055654be8cb044afac721921dde5f4c3bfa9ee7bdf27560  plant-TRI-Q-c.lean.txt
66a9f398b82d4dd29c00f71748e46d48db68ed82c3b98222e6474af576bf3acb  plant-TRI-Q-c.out
eb969bb60ea3aa180cbfe36b913f5935fe7f9f68357d080fb3ee772981cda428  plant-TRI-W-a.lean.txt
25321cc6eb51c9dcfe01ed5787a41aa04e0935590b9f2651d8625c9b82d554ba  plant-TRI-W-a.out
37fb9202e320121d7ce14d7cf7c7838b90579250285a46a5be59ca4282ff404d  plant-TRI-W-b.lean.txt
752cb7907e976941b0fabf3b5ef0f5deee7336aa53c25a990d075b098f2cc09f  plant-TRI-W-b.out
21de03e402ad262f29e7fab6ffff94d708100f56a35464f98f67b40cfe6b5f4c  plant-TRI-X-a.lean.txt
1ff214a9100f2e99821dda332439a7bb2282e51ffbb034b7ee7a226b51497dfb  plant-TRI-X-a.out
2cc08fd7b642498a5cf9290e43b4d1a0454754365c9c140b8354f7c62be163e3  plant-TRI-X-b.lean.txt
b5c4d4ed6d5cf21c516d3a2be384f81bd7253864fc60f18f154e289d01d7717f  plant-TRI-X-b.out
05f937aaf1b75e888903c41975421da13e8462f52b7800f88cf557ed0cdf28ba  plant-TRI-X-c.lean.txt
93fac1874b65f3e29e923be78013466980a5a7950b098f69a13fdd4fcaf50075  plant-TRI-X-c.out
150213c714e738eaed296adda38f1c8949fd5ebbd2c01ba91ba14b93952dbfa7  plants_tri.py.txt
3a61b462c9aec689ae0373a4ceb3d9db4845b5cecc3b77d8be7b3efc4c7cbc33  witness-TRI-K-a.lean.txt
140f782a806937d84cf96d33281cd2325c5b4e50c238b05ef9a60c0977e450fc  witness-TRI-K-a.out
ce727f7460dc666136084412a9a3ccf330a66f3ee5059bfddf74ff183f0e736b  witness-TRI-K-b.lean.txt
e7d9700a660c04a692aa1f925d8a29906ad65d7655495c763cf26c0f817f9639  witness-TRI-K-b.out
d73ab443f7f3d9328fd3fc4e1659ce44006edadb27441a68cd8094183dd0b941  witness-TRI-Q-a.lean.txt
f39a5ea48fd81b2ebfc723269b0aa17f89cdf9f5b4de2174134349c21f35c50d  witness-TRI-Q-a.out
e5424215c024090c50196c2fd36bcd49a7c9dcc20b808ed5f8990b37c5c68793  witness-TRI-Q-b.lean.txt
83874018fe8faad716d1c0c1c3d1137be8054ec7220af8ddb8c85729fad48ec5  witness-TRI-Q-b.out
10bd972f4d0a26ca614f2f852bf6693e5dee06a68f5d9c71d108ab32931310c2  witness-TRI-Q-c.lean.txt
c5bc08cb92559b5c0349c3eb4a27e2f844e58667f0d3f2c8ce896e6659e58514  witness-TRI-Q-c.out
78a3bd30b542a2cad05828016b4decd002ff537d8a6075063f5c75286fb691cf  witness-TRI-W-a.lean.txt
cbce7c34935bf902790638c108c3069ed0191621f151abe4bfe356698f1f367f  witness-TRI-W-a.out
c3b3bd095e11c090c3176333ba2d247b657412c5844698b4cf54162db44b5504  witness-TRI-W-b.lean.txt
43c5242cfcaf1983d93601bdb6869b93a43cbd3572ba37a5d0be8e2864219461  witness-TRI-W-b.out
2570c4950925ca77f735bea828d41dba42a8b034854397a901124067c99aef82  witness-TRI-X-a.lean.txt
b38fb59883e3f98cfcdf247b04b5aceda69c29a84b6a42d227933ccec79cdfb1  witness-TRI-X-a.out
f0e62428f220f728a8378539f2116fb88b7876c1a75bd3bf513adb7d89aed72a  witness-TRI-X-b.lean.txt
a0a0aa645fcf84b5de562466bc344c6835c3c8186492ee7aa8eb82187aed902d  witness-TRI-X-b.out
38b0c8d69e400fbfbd7f6755252f32f45aea12410eb7d9ed5a18414882e36a11  witness-TRI-X-c.lean.txt
8870ae932c16dcacffca5d52bc84977e12d4c3f4996d281813d440b3207ae799  witness-TRI-X-c.out
```
