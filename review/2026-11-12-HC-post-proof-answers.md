# Answers to the post-proof and adversarial reviews of batch HC, the plasma consumers and the DNLS scoping

Three fresh-context referees read the proved batch HC at 5a5f714. They were: post-proof A (fidelity), post-proof
B (mathematics), and an adversarial referee covering HC, the plasma consumers (`examples/consumer/ConsumerColdPlasma.lean`,
`examples/consumer/ConsumerPhaseMixing.lean`) and `docs/design/dnls-scoping.md`.
- None ran Lean, because the replay was running (lessons 28).
- All are Claude instances, like the lead.
- Their prompts and reports are not recorded (lessons 46). Each finding is restated below in the lead's words.

## Verdicts

| | Post-proof A | Post-proof B |
|---|---|---|
| TdF | FAITHFUL, scope full | FAITHFUL; P-fubini, `integrand_prod`, `tdF_of` SOUND |
| TdE′ | FAITHFUL, scope full | FAITHFUL; `tdEp_of` SOUND |

Neither post-proof referee raised a BLOCKER or MAJOR.

Post-proof B explained why Mathlib's finite-index Fubini needs no integrability hypothesis. If the product is not
integrable, some factor is not, and both sides are 0 under the Bochner convention. It also confirmed that the
continuous factors here make the classical theorem apply.

B's numerical check agrees with the lead's `numerics/review/hc_interface_checks.py`. Direct d = 2 and d = 3 kernels, with
no factorisation, match ∏ I to 1e−14, with Sobol QMC as a third method. The lead's own maximum discrepancy is 2.9e−11.

## Adversarial findings and answers

1. **MAJOR, agreed: the DNLS scoping maths was wrong at d = 3 and silent for d ≥ 4.** The condition "σ < 1 and
   σ(2p − 1) > 1" is only sufficient. Splitting the Duhamel integral at t/2 gives decay whenever a = σ(2p − 1) > 1, in
   every dimension:
   - at σ = 1 the logarithm is absorbed by (1 + t)^{−a};
   - for σ > 1 the near part is integrable.

   So:
   - d = 3 works for p ≥ 2;
   - every d ≥ 4 works for every p ≥ 1;
   - only d = 3, p = 1 is borderline.

   Checked numerically (`numerics/review/hc_interface_checks.py` H3):
   - bounded at (σ, a) = (1/3, 5/3), (2/3, 2), (1, 3) and (4/3, 4/3) (d = 4, p = 1);
   - the control (1, 1) grows like log t.

   `docs/design/dnls-scoping.md` (with a dated revision note) and the ROADMAP candidate row are corrected. The candidate
   statement now covers every d ≥ 1 with (d/3)(2p − 1) > 1. The case σ > 1 also needs a ≥ σ, which holds because
   p ≥ 1.
2. **MAJOR (evidence for the order claim): the referee windows looked too short, and their times were not recorded.**
   Agreed that they were not recorded. The lead's session record has each subagent's launch and finish time (UTC); git
   cannot show them. Every referee of this batch:

   | Referee | Launched at commit | Launched | Finished | Run time |
   |---|---|---|---|---|
   | Pre-proof A | 80a8f50 (freeze, 12:14:07) | 12:14:25 | 12:18:24 | 239 s |
   | Pre-proof B | 80a8f50 | 12:14:35 | 12:19:54 | 319 s |
   | Route | 11652d7 (route, 12:48:21) | 12:48:34 | 12:50:18 | 105 s |
   | Post-proof A | 5a5f714 (proof, 12:59:26) | 12:59:42 | 13:01:58 | 136 s |
   | Post-proof B | 5a5f714 | 12:59:48 | 13:02:04 | 135 s |
   | Adversarial | 5a5f714 | 12:59:58 | 13:05:36 | 336 s |

   - Each referee finished before the next commit: the pre-proof answers are 8e4f8c5 (12:28:33), and the route answers
     are 85d1748 (12:50:38). The part (P-fubini) was first written at 12:50:49, after the route referee finished.
   - No commit was made between 5a5f714 and this answers file. The post-proof and adversarial referees therefore read an
     unchanged tree while the replay ran.
   - An earlier draft of this answer gave 228 s for pre-proof A. The session record gives 239 s; the table is
     corrected.
   - The windows are short because the batch is small: two statements, one part of a few lines, and an assembly. The
     post-proof reads (about 2¼ minutes each) are disclosed as such; the replay is the machine evidence.

   From now on, the answers files record each referee's launch commit and run time (lessons 48).
3. **MINOR, agreed: the scoping doc overclaimed.** Only the kernel bound is machine-checked, not the bound for the
   group. Corrected. The identification of the kernel with e^{itΔ} is a planned lemma.
4. **MINOR, noted: a stale claim in the sanity header** (`OscInt/Front/HypercubicSanity.lean`, data list: "a threshold
   on t added is detected" at d = 1, t = 1/8). The theorem docstring and the plant record already say otherwise. As for
   batch LE (lessons 39 in spirit), the replayed Lean source is not edited after the replay; this answer is the
   correction.
5. **MINOR, done: the prior-art row was stale.** `docs/prior_art.md` now says proved and replayed.
6. **MINOR, done: references and conventions in the scoping doc.**
   - The 2p + 1 ≥ 7 scattering result is attributed as a web-search summary of a 2012 paper by Mizumachi reports it
     (title and venue not recorded; CITED-UNREAD).
   - The threshold is stated for real p, p > (1 + 3/d)/2, and then for integer p.
   - "The two papers must be read" now names the two papers.
   - The Zulip thread: its URL was not recorded in this session and the thread was not read. It is now marked as known
     only from a web-search summary (CITED-UNREAD), instead of being given a locator.
   - λ ∈ ℝ and the integer p are stated.
   - "Flat-band" is replaced by "standing-wave (breather)", with the equation φ satisfies and the sign remark (FOLKLORE).
7. **NIT, done: the gyroaverage constant is rounded up to 1.548** (C*/(2π) = 1.54730…).
8. **NIT, done: numerical interface check.** `numerics/review/hc_interface_checks.py` (H1–H3), with a record. Before
   commit, the lead added the d = 4 case to H3; it exposed that the first draft's absolute cut-off (3) was arbitrary, so
   the test now checks how the decade increments behave (see the script's docstring).
   - The script now prints its Python and numpy versions at run time. The LE2 record
     (`numerics/results-le2-interface-checks-2026-11-11.txt`) gives "numpy 2.3.5", but that was copied from the script's
     docstring, not read at run time. This container has numpy 2.5.3, and the version used on 2026-11-11 is not known.
     The LE2 docstring is corrected; the LE2 record is left as written, and this answer is its correction.
9. **NIT, done: consumer wording.** The uniformity is over profiles supported in a fixed compact set with a fixed C^N
   budget. The cold-plasma consumer treats one frequency branch, e^{−iτω}.

## Post-proof A and B, minor points

- **A: no log for the pre-replay checks.** The replay log (`docs/replay/2026-11-12-session10-HC-verify-all.txt`) is the
  record.
- **A: stale prior-art row.** Same as adversarial 5.
- **A: "useful from 3.70" holds for d ≥ 1.** Fixed in `docs/api/annotations.json`.
- **A: the "Schrödinger group" docstring.** The normalisation is statements.md modelling choice 5. Not edited after the
  replay.
- **B: unused continuity hypothesis; the `EuclideanSpace` identification not stated.** Both noted.
