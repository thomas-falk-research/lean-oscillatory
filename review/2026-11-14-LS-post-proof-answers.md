# Answers to the post-proof reviews of batch LS (LS-E, LS-K, LS-D, LS-D′), 2026-11-14

Subject: the batch LS proofs integrated at d760beb (`review/2026-11-14-external-R4-answers.md`), read at be24b9f,
whose Lean content equals that of 1bc377b, the replayed commit (`docs/replay/2026-11-14-session11-LS-verify-all.txt`).
- Three fresh-context referees: A (fidelity), B (mathematics) and an adversarial referee. All are Claude instances,
  like the lead.
- A and B were blind. Each read a snapshot of be24b9f without `review/`, `docs/STATUS.md`, `docs/HANDOFF.md`,
  `docs/replay/`, `CHANGELOG.md` and `docs/prior_art.md`, so it saw none of the lead's verdicts. The adversarial referee
  read the whole tree, read-only.
- Their prompts and reports are not reproduced (lessons 46). Each finding is restated below in the lead's words,
  with the answer.
- Written by the session-11 lead.

## Times (lessons 48)

From the session record (UTC). The three were launched together, after the replay had ended (19:12:29) and after
be24b9f was pushed; the launch result came back at 19:27:18. No referee ran Lean, `lake` or `make`. The lead made no
change to the tree while they ran: the first edit after the launch is at 19:39:04.

| Referee | Launched at commit | Launched | Finished | Run time | Lean run? |
|---|---|---|---|---|---|
| A, fidelity | be24b9f | 19:27:18 | 19:30:32 | 194 s | no (files, `grep`, Python with SciPy) |
| B, mathematics | be24b9f | 19:27:18 | 19:30:51 | 213 s | no (files, Python: quadrature, mpmath, SymPy) |
| adversarial | be24b9f | 19:27:18 | 19:35:42 | 504 s | no (files, read-only `git`, `sha256sum`) |

## Verdicts

- **A (fidelity):** FAITHFUL for all four statements, full scope; no BLOCKER, MAJOR or MINOR.
  - Each frozen Prop matches `docs/statements.md`: quantifiers, the solution notion, the sign `u′ = iΔu`, the kernel
    normalisation, the constants C* and τ, t ≠ 0 in LS-D and every t in LS-D′, d = 0 included.
  - A computed the kernel against a matrix exponential on a ring of 201 sites (d = 1, t = 1.7): agreement to about
    1e−15.
  - No vacuity: LS-E is proved, so the solution notion is satisfiable, and the sanity layer shows that it is not
    trivially satisfied.
  - The four public theorems have exactly the frozen types, checked by Expr equality in `StatementTypes.lean`.
  - The proof files contain no axiom, instance, attribute, option, `sorry` or syntax extension.
  - The frozen files' SHA-256 values match the stamp manifest.
- **B (mathematics):** all nine parts and the assembly SOUND; no BLOCKER, MAJOR or MINOR.
  - B summarised each part's argument and checked it independently.
  - B's PDE check: the residual of u′ − iΔu for the kernel convolution, with compactly supported data at d = 1 and 2,
    is 1e−11 to 1e−10. It is of order 1 when the sign, the gauge e^{−2idt} or the factor 2 in K_d(2t, ·) is changed.
  - Agreement with the matrix exponential on periodic boxes to 5e−16.
  - Σ|Lₙ| = (4d)ⁿ exactly for n ≤ 5, d ≤ 3, so the stencil bound is attained.
  - The envelope identity and inequality hold to 40 digits for d ≤ 8, including the edge cases d = 0, t = 0 and
    |t| = τ.
- **Adversarial:** no defect in the Lean trust chain (statements, proofs, comparator, replay). One BLOCKER (the reviews
  themselves), three MAJOR, six MINOR, five NIT on records and process. Answered below.

## Answers to the adversarial referee

1. **BLOCKER, answered by this file: the post-proof reviews had no answers file.** It exists now. The STATUS rows did
   not claim "as stated", and they still do not (see 4).
2. **MAJOR, agreed and done: stale and contradictory records.**
   - The Replay column of the four LS rows still said "pending". It now gives the record, as the other batches do.
   - Brought up to date: the README status paragraph, `docs/which-theorem.md`, the evidence paragraph of
     `docs/proof-LS.md`, the prior-art claim, the CHANGELOG "Unreleased" section (it said nothing, although `proved_by`
     changed at d760beb) and the HANDOFF next steps.
   - The be24b9f commit message said these records were updated. Several were not. The lead's grep for stale
     wording missed the phrasings "isolated full replay", "still pending" and "Evidence so far".
3. **MAJOR, agreed and done: the "32 mechanical changes" could not be checked from the repository.**
   - The diff between the packet's ten files and the integrated ones is now committed as
     `docs/replay/2026-11-14-LS-packet-repairs.diff`. It is code, not conversation, so lessons 46 does not exclude it;
     the drafted code is already in the tree, disclosed. Its header gives the method, so it can be reproduced from the
     archive (SHA-256 6acdfc63…).
   - Count, re-derived by the lead from the archive: 33 diff regions (Op 6, Exp 1, Stencil 7, FourierStencil 9,
     Series 4, Conv 4, Bound 1, Envelope 1, Unique and Final 0). The agents' 32 counts the last two FourierStencil
     regions as one change (a `convert … .integrable` and the `simp only` it needs).
   - The two changes the referee singled out:
     - Exp: `zero_smul` does not unify with two ℝ-actions on the operator space. It is replaced by a pointwise proof of
       the same equation (0 : ℝ) • (I • A) = 0 and a `beta_reduce`. The lemma proved and the route are unchanged, so the
       lead keeps the label "mechanical".
     - Op: the draft's `change` gains parentheses and a type ascription. The lead checked whether the draft's
       `∑ j, a + b − c` parsed differently from `∑ j, (a + b − c)`, which would have made the draft's operator wrong. It
       does not: Lean's big-operator notation takes the whole sum term (compiled probe: `∑ _i : Fin 2, 1 + 1 − 1` is 2,
       not 1). The parentheses only align the term with the ascription.
   - Two inaccuracies, corrected here:
     - The d760beb commit message called the final file "byte-identical to the packet's". Its code is; its copyright
       header and module docstring were replaced, like every file's.
     - The commit message's list of fix kinds omitted the Exp workaround. The diff header now lists every kind.
4. **MAJOR, agreed and done: the four final theorems had no docstrings (CONTRIBUTING step 11).**
   - `OscInt/Front/LatticeGroupFinal.lean` now gives each theorem a docstring with the statement, the label, and where
     the classical result is (the kernel formula for d = 1: Stefanov–Kevrekidis, arXiv nlin/0409009, eq. (6), as
     `docs/statements.md` cites it).
   - The example requirement of step 11 was already met: `examples/api/Snippets.lean` has the four type examples, as
     for batch HC.
   - The docstrings change Lean after the accepted replay. So the rows say "as stated" only after an isolated
     `make verify-all` of the commit that adds this file, as the referee says. No waiver.
5. **MINOR, done: the sanity layer did not pin the gauge or the factor 2 semantically.**
   - The pre-proof answers deferred the unconditional pin to the proof of LS-K. With LS-E and LS-K proved, the new
     consumer example `examples/consumer/ConsumerLatticeSchrodinger.lean` (built by `make quick`) proves, unconditionally:
     - ∂ₜG_1(0, 0) = −2i;
     - ∂ₜG_1(0, e₁) = i, and that it is not i/2.
   - What the mutated kernels would give is a hand computation, stated as such in the file and checked numerically by
     the lead (mpmath, central differences): i/2 without the factor 2, and 0 without the gauge.
   - Why not in `LatticeGroupSanity.lean`: the plant harness compiles that file against planted statements, against
     which the final theorems cannot be built. So the sanity file is unchanged, and its hash still matches the plant
     record.
   - Its header says the gauge and the factor 2 are "not tested semantically", while its later section adds the
     conditional derivative theorems. These are two statements about the sanity layer, not a contradiction. The
     consumer file is the semantic test.
   - The strengthening plants D-rate, D-const-half and Dp-rate rest on floating-point evidence only. Noted, as the
     referee says; this is acceptable now that the statements are proved.
6. **MINOR, done: the proofs imported a sanity module.**
   - `LatticeGroupBound.lean` now proves the box volume locally (`box_volume`, the same two-line proof as
     `hypercubeBox_volume`).
   - The unused import of `OscInt.Front.HypercubicSanity` in `LatticeGroupFourierStencil.lean` is removed (B, NIT 2).
   - No sanity module is now imported by `OscInt.Front.LatticeGroupFinal`, directly or transitively (checked by
     walking the import graph). A fresh build of `OscInt.API` passes.
7. **MINOR, for the owner: authorship and licence of the drafted files.**
   - The ten files carry the project's copyright and Apache-2.0 header, as the A3 files did.
   - No licence grant from the external reviewer is recorded in the repository.
   - This is the owner's decision, not the lead's. It is listed for the owner in the HANDOFF.
8. **MINOR, agreed and done: two verbatim phrases of the packet were quoted in the R4 answers (lessons 46).** Both are
   paraphrased.
9. **MINOR, agreed and done: the replay record over-stated two things.**
   - The `lean` step built nothing new: Lake reused the build products and re-printed their stored warnings. So the
     warnings were reported 18 times, not produced by 18 elaborations. This is not a soundness issue: the stale-build
     check passed and the kernels re-check the exported declarations.
   - The post-run clean-tree claim comes from the lead's check at 19:12:47 in the session record, not from the log.
   - Both are corrected by a dated note in the record's header. The A3 record of 2026-11-13 uses the same "elaborated"
     wording; it is corrected here, not edited.
10. **MINOR, done: HANDOFF wording.** The "Integrated" bullet gives the old and the current state. The next-steps
    condition is now "the replay passed and no review finding is open", which covers all three referees.

NIT answers:
- **Threshold.** `docs/api/annotations.json` now says the decaying part beats 1 exactly for |t| > τ ≈ 1.852, instead
  of the sufficient |t| > 1.853.
- **Lessons 50.** It now calls the reclaim-after-idle mechanism the likely cause, seen twice, and adds that the third
  run, with the session kept busy, survived 3 h 11 min. The first partial record's "container restart" describes the
  same event.
- **Kernel side.** `docs/proof-LS.md` now says the Bound and Envelope repairs were made by the operator-side agent;
  the packet groups those files with the kernel side.
- **Model names.** The prior-art rows describe different packets and name each tool as given for that packet. No
  change.
- **STATUS paragraph.** The batch LS paragraph now carries "Reviewers are AI agents; no human has read these
  statements".

## Answers to the NITs of A and B

- **A N1 and B NIT 3: proofs depending on a sanity lemma.** Done; see 6.
- **A N2: `StatementTypes.lean` changed since the stamp.** Expected: the four `#assert_type_is` lines were added
  for batch LS. The checking elaborator is unchanged.
- **B NIT 1: the route said "without deviation".** The P-fourier base case uses TdF at t = 0 (which is
  `tdF_of hcFubiniFacts`), not `hcFubiniFacts` directly. `docs/proof-LS.md` now records this equivalent substitution.
- **B NIT 2: unused import.** Removed; see 6.
- **B NIT 4: the route's operator versus the code's.** The route writes Σ_j(S_{e_j} + S_{−e_j}) − 2d·id; the code
  distributes −2·id into each term. They are the same operator. No change.

## Addendum: a check of the post-review delta (b4300ff)

A fourth fresh-context referee read the diff from be24b9f to b4300ff (Lean, Makefile, examples) and this file,
read-only and without Lean. It was launched at b4300ff at 19:56:15 UTC and finished at 20:02:15 (360 s, session
record). The last 15 s of the `make quick` of b4300ff (which ended at 19:56:30 and passed) overlapped its start;
`make quick` changes no tracked file. The lead pushed b4300ff at about 19:57 and made no tree edit while it ran.
- **Verdict:** no BLOCKER, MAJOR or MINOR.
  - The four docstrings are correct against the frozen statements. Numerically G_1(t, z) = e^{−2it} iᶻ J_z(2t) to
    about 1e−16.
  - `box_volume` is the same statement and proof as the sanity lemma.
  - The dropped import removes eight modules from the closure, none of them used. They declare no notation, instance,
    attribute or option.
  - The consumer's three theorems, its hand computation and its `linear_combination` step are right. Each derivative
    pin separates exactly the mutation it names.
  - No claim of this file about the delta is false.
- **NIT, done:** the consumer docstring's "finding 2" was ambiguous. It now says referee A's finding 2 of the
  pre-proof answers, and item 5 here.
- **NIT, done:** "beats 1 exactly for |t| > τ" holds for d ≥ 1 only (at d = 0 the decaying part is 1). Corrected in
  `docs/api/annotations.json`. The same words in `docs/statements.md` are covered by the statement stamps, so they
  stay; this is the note.
- **NIT, noted: the decay-rate attributions differ.**
  - The LS-D docstring credits Stefanov–Kevrekidis with the rate for d = 1 only.
  - `docs/prior_art.md` and `docs/design/torus-lattice.md` credit them with (1 + |t|)^{−d/3} on ℤ^d, as read from the
    arXiv abstract.
  - The docstring is the narrower claim and is true. It stays, since a Lean change now would need its own review.

## What changed, and what remains

- **Lean changes**, all outside the reviewed proof arguments:
  - docstrings on the four final theorems;
  - one import removed from `LatticeGroupFourierStencil.lean`;
  - one import replaced by the local lemma `box_volume` in `LatticeGroupBound.lean`;
  - the new consumer example, added to the `entry-point` target of the Makefile.

  The frozen statements, the Blueprint interfaces and the sanity file are unchanged.
- **Next:** an isolated `make verify-all` of the commit that adds this file, with the watcher and the keep-alive of
  lessons 50. The four rows move to "machine-checked as stated" only if that replay passes with comparator-LS
  accepted, since no review finding remains open.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
