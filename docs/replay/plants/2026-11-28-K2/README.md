# Batch K2: planted controls of the sanity layer (docs/lessons.md, rules 8 and 9)

Written by the sanity-layer agent K on 2026-11-28 (generator run 2026-11-28T01:09:50Z to 2026-11-28T01:12:14Z UTC, generator exit code 0) against
the draft statement text, unchanged:

- `OscInt/Statements/TriangularDecay.lean` at repository HEAD a9418e9efad27729c0779eff630e6e215e9cd803 (unchanged since
  51d8008), SHA-256 32b99c3864b29dd7b22108e08f28926f6c470c68188b9b7b7dcd59e9f3a99cbc (identical to the copy `stmt/TriangularDecay.lean` from which
  the generator reads the statement text; the module itself is the repository's built `.olean`).
- Sanity layer `src/OscInt/Front/TriangularDecaySanity.lean` (module `OscInt.Front.TriangularDecaySanity`, namespace
  `OscInt.API.TriangularDecaySanity`), SHA-256 88b888728d9559e25273096eb5b10ee213f551bf468785180a5af974304d8ede.
- Generator `plants_k2.py.txt` (= `gen/plants_k2.py`), SHA-256 1f5ca0d2b91f2c6c77b1725b819838877c9696acc048e009c6866a819afff06f.

Harness: `.lake/build/lib/lean/OscInt` mirrored (symlinked files, real directories) into `lib/`, placed first on
`LEAN_PATH` before the repository's `lake env` path; the sanity module compiled with `--root=src -o lib/...olean`
(`lean.sh`, `nice -n 10`, `-DautoImplicit=false`; Lean 4.35.0, Mathlib 56a005855ea1). Each generated file imports
`OscInt.Front.TriangularDecaySanity`; the witness of L-a also imports the built `OscInt.Front.Core`, for the proved
amplitude lemma F1 (`OscInt.API.ampBoundOfContDiff`) only. One Lean process at a time. Nothing in the repository
was written.

Method (as batches SPL and TRI). For each plant: `ok-` = unplanted copy `P_<Statement>` followed by copies (renamed
`P_`) of every sanity theorem that takes that statement constant as a hypothesis; must compile. `plant-` = the same
with ONE textual mutation; its rejection by the copied scripts is recorded and is never counted as a detection.
`witness-` = the planted copy and compiled theorem(s), with `#print axioms` (only propext, Classical.choice,
Quot.sound, checked by the generator). Kinds: `not` (¬ planted, from unconditional data) DETECTED; `rel` (true
statement → ¬ planted) DETECTED RELATIVE TO THE TRUE STATEMENT; `weak` (draft → planted) TRUE WEAKENING; `char` NOT
DETECTED, with a compiled characterisation of what a detection would have to refute. No file proves, or uses a proof
of, a batch-K2 statement.

## Outcome

15 plants, at least one per statement: 7 DETECTED (ML-a, ML-b, MA-a, MA-b, MA-c, F-b, U-c), 4 DETECTED RELATIVE TO
THE TRUE STATEMENT and NOT DETECTED unconditionally (L-a via K2-ML; U-a, U-b via K2-D; D-a via K2-U), 3 TRUE
WEAKENINGS (L-b, U-d, D-b), 1 NOT DETECTED (F-a). K2-D has no unconditional detection. All 15 unplanted copies
compile; 14 planted copies are rejected by the copied scripts and one (ML-a) is accepted by them (script-only either
way, not counted).

| plant | statement | mutation | outcome | evidence |
|---|---|---|---|---|
| ML-a | K2-ML | threshold `96 r^{1−m}` ↦ `0 r^{1−m}` | DETECTED | `ml_threshold_bite`: `m = 2`, `t = 1/200²`, `plat 1 2`: claim `200/48`, but `‖∫‖ ≤ 4` |
| ML-b | K2-ML | `/(24m)` ↦ `/(m/40)` | DETECTED | `m = 6`, `t = (5/2)⁶` (`t^{5/6} = 97.6 ≥ 96`), `plat 1 (5/4)`: claim `8/3`, `‖∫‖ ≤ 5/2` |
| MA-a | K2-MA | `Re C ≥ 1/(12m)` ↦ `Re C ≥ 12/m` | DETECTED | own remainder at `m = 2`, `t = 1`, `plat 1 (5/4)`: `‖C‖ ≤ 9/2 < 6` |
| MA-b | K2-MA | remainder `r^{m−1}` ↦ `r^m` | DETECTED | `m = 2`, `r = 10⁶`, `t = 10⁻¹⁶`: `‖C‖ ≤ 0.0402 < 1/24 ≤ Re C` |
| MA-c | K2-MA | hypothesis `0 < t` dropped | DETECTED | `ma_time_zero_bite`: at `t = 0` the bound reads `∫ b ≤ 0`, `∫ plat 1 2 ≥ 2` |
| L-a | K2-L | hypothesis `D²Ψ(k₀)[w, w] ≠ 0` dropped | REL. (K2-ML) / NOT DET. uncond. | `x²` at `0`, amplitude `b(κ₁)b(κ₂)`: factorises; K2-ML gives `t^{−1/2}` against the claimed `t^{−1}` |
| L-b | K2-L | spanning hypothesis dropped | TRUE WEAKENING | `span_of_hyps`: spanning follows from the other hypotheses; draft → plant (equivalent) |
| F-a | K2-F | support condition `tsupport χ ⊆ (−π, π)²` dropped | NOT DETECTED | compiled: plant → the unlocalised bound at `χ = 1`; no phase refuting it constructed |
| F-b | K2-F | hypothesis on all `n` ↦ on `n ≠ 0` | DETECTED | zero phase: coefficients `0` off `n = 0`, so `B = 0`; `∫ χ₁ > 0` |
| U-a | K2-U | `t^{−triRate α}` ↦ `t^{−3/4}` | REL. (K2-D) / NOT DET. uncond. | `α = 0`: `c t^{−2/3} ≤ ‖K‖ ≤ C t^{−3/4}` (`rate_separation`) |
| U-b | K2-U | in `triRate`, `\|α\| = a*` ↦ `α = a*` | REL. (K2-D) / NOT DET. uncond. | `α = −a*`: planted rate `3/4`, K2-D gives `2/3` |
| U-c | K2-U | hypothesis `1 ≤ t` dropped | DETECTED | `u_time_zero_bite`: `‖triKernel 0 0 (0, 0)‖ = (2π)² > C · 0^{−2/3} = 0` |
| U-d | K2-U | `t^{−triRate α}` ↦ `t^{−2/3}` | TRUE WEAKENING | draft → plant, compiled (`triRate ≥ 2/3`, `t ≥ 1`) |
| D-a | K2-D | `t^{−triRate α}` ↦ `t^{−2/3}` | REL. (K2-U) / NOT DET. uncond. | `α = 1/4`: `c t^{−2/3} ≤ ‖K‖ ≤ C t^{−3/4}` |
| D-b | K2-D | `t^{−triRate α}` ↦ `t^{−3/4}` | TRUE WEAKENING | draft → plant, compiled (`triRate ≤ 3/4`, `t ≥ max T 1`) |

Why the rate plants of K2-U and K2-D are not detected unconditionally: refuting a wrong exponent needs a lower bound
(for K2-U) or an upper bound (for K2-D) of `triKernel α t n` at large `t`, i.e. the content of the other statement of
the pair; neither is proved before the proofs exist. The witnesses are therefore relative (U-a, U-b, D-a), or the
plants are implied by the draft (U-d, D-b). Why L-a is only relative: refuting it needs the lower bound
`|∫ b e^{itx²}| ≳ t^{−1/2}`, which is K2-ML's content (not proved here). Why ML-b detects only a gross change: the
draft's `1/(24m)` is `37m` to `46m` times below the true asymptotic constant (`85` times at `m = 2`) (see the report, finding K-4), and
without an oscillatory upper bound (a lemma of K2-MA's proof, not written) only the trivial bound `‖∫ b‖ ≤ 2R` is
available; a planted constant between the truth and `40/m` is NOT DETECTED. Why F-a is not detected: a refutation
needs continuous biperiodic phases whose lattice coefficients are all small while the box integral at a non-integer
velocity is comparatively large (a logarithmic divergence of the Dirichlet-type coefficients of `1_box e^{iq·k}`
suggests the plant is false, but no such phase is constructed; its truth is not decided here).

## Generator log (SUMMARY.txt)

```
ok-ML-a: accepted (want accepted) [3.6 s]
plant-ML-a: accepted (want recorded) [3.7 s]
witness-ML-a: accepted (want accepted) [3.3 s]
  ML-a [the threshold constant 96 ↦ 0]: DETECTED (witness compiled: ¬ planted statement)
ok-ML-b: accepted (want accepted) [3.7 s]
plant-ML-b: rejected (want recorded) [3.7 s]
    first error: plant-ML-b.lean:22:2: error: Tactic `apply` failed: could not unify the conclusion of `h1`
witness-ML-b: accepted (want accepted) [3.3 s]
  ML-b [the constant 1/(24m) ↦ 40/m]: DETECTED (witness compiled: ¬ planted statement)
ok-MA-a: accepted (want accepted) [3.3 s]
plant-MA-a: rejected (want recorded) [3.4 s]
    first error: plant-MA-a.lean:25:12: error: Application type mismatch: The argument
witness-MA-a: accepted (want accepted) [3.3 s]
  MA-a [the bound Re C ≥ 1/(12m) ↦ Re C ≥ 12/m]: DETECTED (witness compiled: ¬ planted statement)
ok-MA-b: accepted (want accepted) [3.4 s]
plant-MA-b: rejected (want recorded) [3.4 s]
    first error: plant-MA-b.lean:25:28: error: Type mismatch
witness-MA-b: accepted (want accepted) [3.7 s]
  MA-b [the remainder 4/(m t r^{m−1}) ↦ 4/(m t r^m)]: DETECTED (witness compiled: ¬ planted statement)
ok-MA-c: accepted (want accepted) [3.4 s]
plant-MA-c: rejected (want recorded) [3.5 s]
    first error: plant-MA-c.lean:25:28: error: Function expected at
witness-MA-c: accepted (want accepted) [3.3 s]
  MA-c [the hypothesis 0 < t dropped]: DETECTED (witness compiled: ¬ planted statement)
ok-L-a: accepted (want accepted) [3.3 s]
plant-L-a: rejected (want recorded) [3.3 s]
    first error: plant-L-a.lean:24:63: error: Application type mismatch: The argument
witness-L-a: accepted (want accepted) [4.4 s]
  L-a [the hypothesis D²Ψ(k₀)[w, w] ≠ 0 dropped]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-L-b: accepted (want accepted) [3.3 s]
plant-L-b: rejected (want recorded) [3.3 s]
    first error: plant-L-b.lean:24:60: error: Application type mismatch: The argument
witness-L-b: accepted (want accepted) [3.2 s]
  L-b [the spanning hypothesis dropped]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-F-a: accepted (want accepted) [3.1 s]
plant-F-a: rejected (want recorded) [3.2 s]
    first error: plant-F-a.lean:25:2: error: Function expected at
witness-F-a: accepted (want accepted) [3.1 s]
  F-a [the support condition dropped]: NOT DETECTED (compiled characterisation of what a detection would have to refute; no refutation)
ok-F-b: accepted (want accepted) [2.8 s]
plant-F-b: rejected (want recorded) [3.1 s]
    first error: plant-F-b.lean:26:2: error: Type mismatch
witness-F-b: accepted (want accepted) [2.9 s]
  F-b [the zero mode n = 0 dropped from the hypothesis]: DETECTED (witness compiled: ¬ planted statement)
ok-U-a: accepted (want accepted) [2.8 s]
plant-U-a: rejected (want recorded) [3.1 s]
    first error: plant-U-a.lean:18:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
witness-U-a: accepted (want accepted) [3.2 s]
  U-a [triRate ↦ 3/4 (exceptional branches dropped)]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-U-b: accepted (want accepted) [2.8 s]
plant-U-b: rejected (want recorded) [2.8 s]
    first error: plant-U-b.lean:18:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
witness-U-b: accepted (want accepted) [3.2 s]
  U-b [in triRate, |α| = a* ↦ α = a* (the branch −a* dropped)]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-U-c: accepted (want accepted) [2.8 s]
plant-U-c: rejected (want recorded) [2.8 s]
    first error: plant-U-c.lean:17:10: error: Function expected at
witness-U-c: accepted (want accepted) [2.7 s]
  U-c [the hypothesis 1 ≤ t dropped]: DETECTED (witness compiled: ¬ planted statement)
ok-U-d: accepted (want accepted) [3.1 s]
plant-U-d: rejected (want recorded) [3.1 s]
    first error: plant-U-d.lean:18:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
witness-U-d: accepted (want accepted) [2.8 s]
  U-d [triRate ↦ 2/3 everywhere]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
ok-D-a: accepted (want accepted) [3.2 s]
plant-D-a: rejected (want recorded) [2.8 s]
    first error: plant-D-a.lean:17:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
witness-D-a: accepted (want accepted) [3.2 s]
  D-a [triRate ↦ 2/3 everywhere]: DETECTED RELATIVE TO THE TRUE STATEMENT (witness compiled: true statement → ¬ planted statement); NOT DETECTED unconditionally
ok-D-b: accepted (want accepted) [2.7 s]
plant-D-b: rejected (want recorded) [2.8 s]
    first error: plant-D-b.lean:17:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
witness-D-b: accepted (want accepted) [2.8 s]
  D-b [triRate ↦ 3/4 everywhere]: TRUE WEAKENING (compiled: draft statement → planted statement); no datum can refute it
```

## File hashes (SHA-256)

```
c6242a78eabb86facb5308f76d890dd4eccd82fb0221056dff21f0b1bf9216bd  SUMMARY.txt
e5c664708061fe3748bd2bfedb42d3105ef51e6e04a3c41b63e26ff586783a52  ok-D-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-D-a.out
e5c664708061fe3748bd2bfedb42d3105ef51e6e04a3c41b63e26ff586783a52  ok-D-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-D-b.out
8c7b5091f52dcd5aed42381cc1e34de23308c4d9a35a9f984ecef4b2a61d2585  ok-F-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-F-a.out
8c7b5091f52dcd5aed42381cc1e34de23308c4d9a35a9f984ecef4b2a61d2585  ok-F-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-F-b.out
76569934637b81bae89b8e4d28d550e1148a643ab54d044ddc7bbf21284f1c03  ok-L-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-L-a.out
76569934637b81bae89b8e4d28d550e1148a643ab54d044ddc7bbf21284f1c03  ok-L-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-L-b.out
69cd645a6ce55d438ae711b6e86111158c735e89de0b800577f021d1d8c2b157  ok-MA-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-MA-a.out
69cd645a6ce55d438ae711b6e86111158c735e89de0b800577f021d1d8c2b157  ok-MA-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-MA-b.out
69cd645a6ce55d438ae711b6e86111158c735e89de0b800577f021d1d8c2b157  ok-MA-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-MA-c.out
02da7cdce3ef798a8dac83f2f5c8f81e4f6a08e7f3b70066f2635a0e2a42ae47  ok-ML-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-ML-a.out
02da7cdce3ef798a8dac83f2f5c8f81e4f6a08e7f3b70066f2635a0e2a42ae47  ok-ML-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-ML-b.out
ea00237e8ef37cd36b0706a59f0ec9a79bda2c61bce0088c08f3804e6ce198c9  ok-U-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-U-a.out
ea00237e8ef37cd36b0706a59f0ec9a79bda2c61bce0088c08f3804e6ce198c9  ok-U-b.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-U-b.out
ea00237e8ef37cd36b0706a59f0ec9a79bda2c61bce0088c08f3804e6ce198c9  ok-U-c.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-U-c.out
ea00237e8ef37cd36b0706a59f0ec9a79bda2c61bce0088c08f3804e6ce198c9  ok-U-d.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  ok-U-d.out
1185a85cc0a238e89b7fa18fc9b1b88104375b95fb707dd36a083d710709f5ad  plant-D-a.lean.txt
ddbcda1ea60227debd3d746c760218e1b80e679d222e1cdcd17d563856c48465  plant-D-a.out
e9abfbd476f81bc6cc2b76ad48995ef79b598905d8c17d5c77d5901a836ea5e1  plant-D-b.lean.txt
bf545369a039f77b41dcaa17ae3afeb0556ac91701dce60d49506224d3fd51ee  plant-D-b.out
4c52ccda350f1d8e9a51f611b5dbceec4be9167fd9294101c2bb9fb5a62f736a  plant-F-a.lean.txt
aef187b180011d58ef6a8997bb3b122170923b63547613b5c977f58836cd4f1c  plant-F-a.out
ad28d9d503da353af39cec9b42376173f70afc1e9b0bbb378620e5afba852204  plant-F-b.lean.txt
8fe51dc705b532199aed77202fe454c8edcfc9bd4ada949807f215e7eec475c7  plant-F-b.out
6c07f4e08679902dcd0146f0856eca48d4c5dfe4f92117b68d9e0889d68d5666  plant-L-a.lean.txt
b2f622e0fdc0fa4eaae9fd41b8e07f97a389f7a95031c9fbc4851b63a8ab1f32  plant-L-a.out
2c7495ff5f18eb3cdf8c2031d3cd87800e1665a6651f0a26e918d33b6d5536d7  plant-L-b.lean.txt
82d4378598b2460df2989ece291bf832c3fbcf22c93f9af4de8380a232385ebb  plant-L-b.out
02e6021d1304ff2490d6d211ca7f272d6b71624d43243b8748a358fa136d71ba  plant-MA-a.lean.txt
902868578eae0c2bf1b75378876471e6a72de93fc8e1f1c158ba05c3ef3f882f  plant-MA-a.out
46425b60456c09e52206c39ef5f0c2982675201961bd26d9d8590db309a2481e  plant-MA-b.lean.txt
48f1e127db8a140ae605bd91b7de86b78cb348640b36415b443eb3c8cc0ebe87  plant-MA-b.out
0d00bc3f27dd69e2ad31ec0acc5734381aab18f8e5f92258899b2c35e2d9d1a9  plant-MA-c.lean.txt
7f59c806ec83d30d76119c00159468504faa1264a2c264c1f2d0f0b85dd8b7dc  plant-MA-c.out
8a036f7e9e3d15470758dcc29c4dd9d1bddfa80c13524a5566b87244bd618929  plant-ML-a.lean.txt
0f7a4e9988d50573cced70a424e1e9b521c8ceda58dc4f635ac6b14a9e20b9cf  plant-ML-a.out
f23f51babe1bc970d3e4756cba7c493c9f6b24eb13eb89c1922cb672ca0aa02f  plant-ML-b.lean.txt
9dd9edf8a722598f949b337ce65b73620d85e7f07e26419f49271a2c23f69951  plant-ML-b.out
358efe5a0e8c6e6f348c427a4df0d98783f07016bac4fce29bfd0ea1e62b96c5  plant-U-a.lean.txt
23e138aaaf78e8b05abf1dd657c43607f0c071e72089fd107c5c61d78dd8d6e3  plant-U-a.out
4547e604c0798231e071f6fed131722723e34b5171a9822f6655fab845f6ef68  plant-U-b.lean.txt
9220a06971df26362c43c58935485e2cf0b5c14411b197665ad8ef40ad93a5e3  plant-U-b.out
03cd88b36a4b1064b3882d28d6108211bb5b5d19c27b80b20d19c00ed005bc11  plant-U-c.lean.txt
97141b3822ac619e54d85fd59ffb335a5f89c02006803f2aedfae07335ecbdc6  plant-U-c.out
623171ec8796560e9111c823377989a9a495ba3fd448ecdf469bb95d4df1c73b  plant-U-d.lean.txt
bb6a7de4098cf3c0a9345af1c4b31e49048612d6c3a7a17bee106a04b79e7d28  plant-U-d.out
1f5ca0d2b91f2c6c77b1725b819838877c9696acc048e009c6866a819afff06f  plants_k2.py.txt
79854ac472fcb42a819ca122ced121a00e1165285da0add58d0691a738c678d0  witness-D-a.lean.txt
33f6c44df265b54922643184a9129a53e016410d4f96fe930ac0e4d4893b027d  witness-D-a.out
8acf06b6cd5ab472db35ad5d537bdbc5c146c4cac5a0446ece6752655d38ee69  witness-D-b.lean.txt
b910dee0d495e4e8d13be4f18294cb7b70436e8841a0e70c24481ca0855f4287  witness-D-b.out
b7d59d571ca41e6d7242af35fdf4bd0f2bc224fc04ca004b9464b31f19bb5eca  witness-F-a.lean.txt
a96818ea588ee8f13abfedcf6524630d57f0b07a724a0a38404649b8698c95fb  witness-F-a.out
1cc25ff763307bb2ea47db0a2ca759acd21b6951741f317b26ff823806788cdb  witness-F-b.lean.txt
7651d466cc4714c43d188341b290ee995c11449e1c25c98272c409884b2ffd92  witness-F-b.out
3d35c3626b145d18401f09c068ff71569faaefb17e449b700f4cdaccb42d261d  witness-L-a.lean.txt
f791ed119974bac15ba1bcaa7adb472897f14eca7f023bd130f135034ba47247  witness-L-a.out
dcbc322c3c2ce4de62380c11ae5a61afe59a88d5b4d9e0ade2ffcfe572def31e  witness-L-b.lean.txt
ab2e48d7ff32d301e2ce58e796c303527734fb70cc4d91127f9a701797a89358  witness-L-b.out
f0ac18b81803ad1271ea71518c2f7a0121c6b6694799e2b72ea5e83b60a468eb  witness-MA-a.lean.txt
3c0a2ba3a0b898f58843e8fc0aacf9337cb66c22e70ef82e1732bda297704816  witness-MA-a.out
9791995512b05dfb5dacf9e3993f4a12593eee5ebd6b67cbd17776bd9e672235  witness-MA-b.lean.txt
4342e9cd0159a698f01d6ff3aeb6172235191a0c45b2074d8d125d8a42f833c7  witness-MA-b.out
9e26c2c04e4b0ead747e935d5697e79ceaae58d9f2d54ff4c51dfff3ad004986  witness-MA-c.lean.txt
d3ee5ea228dd9f6828a8d644770a3e13ae3e5ce02ac845953305707109fd5a27  witness-MA-c.out
50d62b8712639aae2c5dfe520c0dc710d9db9c72ce1bd33f17e13aca792c1ab1  witness-ML-a.lean.txt
65cedb1d5a04e977721ce496d4f6a743a9cbf2e9161ec020624c3771755671a2  witness-ML-a.out
9a2bbdae29f0e53b27e2f7acc477cdc6ad126b7d225372b4645c9fd366219360  witness-ML-b.lean.txt
bfd20d49a81f11d8d02d6c6ad6e7dc45f972b434dda2294cc53ce467072386ce  witness-ML-b.out
7dc2b9711832166ec19725d5d9a62990f2ccf868480f4a159b24c42b02d2ab0f  witness-U-a.lean.txt
4fe54bffb6ca3bb4dda171c25b1776be24d94ae5b5863336a74d84d4bce128f1  witness-U-a.out
663c1a5ca1b7f6ecaedf96edc99498bdd814a713a9ebe4854c4faec7a811ba68  witness-U-b.lean.txt
b2d684a7f00ba849160f71fe9e85c7e13e3b80ed89c7327be3c22c4f72688d70  witness-U-b.out
57f257fd1182eedee940b44c183af7b673e92e796bb3f927a5e8e28700824d08  witness-U-c.lean.txt
f5f1743898ac754abf4a394947bb9940030d98cd746af0beeb0b17c896ce1138  witness-U-c.out
b941c86808e4fdc91d58f85d8a949bd20c98cda513e4f8b4c3bc44973e83c8dd  witness-U-d.lean.txt
9074164ce6d7248da3fe2086c340e269869b676722927a9b87b3df02a631b2aa  witness-U-d.out
```
