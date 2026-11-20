<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Owner decisions: the SPL branch after v0.7.0; the next batch is the two-saddle lemma (TSD)

Recorded 2026-11-20 (session 13) by the lead. Both decisions were taken by the owner in the session on 2026-11-20,
after the lead had reported the facts and the options; the owner's words are not reproduced.

## Decision 1: what happens to the branch of batch SPL

After v0.7.0 is published and its pins pull request is merged, `main` is merged into
`claude/batch-sp-leading-term` (never rebased: three stamps name commits of that branch) and the branch goes into
`main` as unreleased work, by a merge commit, never squashed. The next release is v0.8.0 (a minor release: the
statement registry changes), cut when the work that follows on from batch SPL is proved, not immediately.

## Decision 2: the next batch machine-checks a lemma that a current research preprint depends on

The lemma: "Two-saddle steepest descent with a uniform remainder", Lemma E.1 of *The spinless modular bootstrap at
large central charge* (hexagon:2611.00174v1, contributed by Anthropic, CC BY 4.0, marked "primarily AI-generated
text", not peer reviewed). Working label of the batch: TSD. It is developed on `claude/batch-sp-leading-term`, as
the decision of 2026-11-19 foresaw for the two-saddle stage.

Facts the lead reported before the decision:

- The preprint's attainment theorem uses the lemma through its Lemma 7.7. The lemma is a statement about an
  integral along a line in a strip where two functions are analytic, with two saddle points that coalesce as a
  parameter approaches an edge; its remainder is explicit. Its proof is four pages in the preprint.
- The preprint's listed source is one TeX file; it does not mention Lean. The announcement that accompanies it
  says its results were verified in Lean; the lead could not find that development or a statement of what it
  covers. The lead read the appendix in the TeX source (SHA-256 of the file
  6e167ddd9f1c8ba46680c9550fd5d84eacf3d9901d02f4c9b22433d63b2db079, as the server lists it).
- The preprint, every lead, prover and referee of this repository are of one model family: nothing in the
  preprint counts here as independent evidence, and a machine check is the kind of evidence that does not depend
  on who wrote the proof.
- What a machine check of the lemma would and would not give: it would check the lemma as an abstract statement
  under its hypotheses (SD1) to (SD4); it would not check that the preprint's own function satisfies those
  hypotheses (its appendix E.4 and sections 7.1 to 7.6), nor the preprint's theorem. The Hankel function is not in
  Mathlib at the pin; the lemma uses it only through an exact factorisation, so it can be a parameter.
- The lead's assessment, asked for by the owner, that this library's own results are formalisations of classical
  mathematics with no claim of novelty, and that verifying a lemma on which new work rests is where its value
  would be largest.

Every rule of `CONTRIBUTING.md` applies from the first step: prior-art gate, a check of the published proof by a
fresh referee and numerics before any statement is drafted, statements with sanity layer and plants, freeze, blind
review, and only then Lean proofs.
