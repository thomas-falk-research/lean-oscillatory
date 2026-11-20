<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Owner decision: v0.7.0 stays as stamped; the next batch (SPL) opens on its own branch

Recorded 2026-11-19 (session 13) by the lead. Both decisions were taken by the owner in the session on 2026-11-19,
after the lead had reported the facts and the options; the owner's words are not reproduced.

## The facts

On 2026-11-19 the owner pointed the lead to two preprints deposited on 2026-11-07 on the preprint server Hexagon
and to the announcement that accompanies them. The lead read the announcement, the abstract, provenance statement,
status table and legend of both preprints, and the statement of Appendix E of the first; not the proofs.

- *The spinless modular bootstrap at large central charge* (hexagon:2611.00174v1, contributed by Anthropic, 131
  pages, CC BY 4.0, marked "primarily AI-generated text"). Its attainment theorem rests on a lemma called there
  "two-saddle steepest descent with a uniform remainder" (its Lemma E.1): the leading term of a one-variable
  oscillatory integral with two stationary points that coalesce at an edge, with a remainder bounded by explicit
  constants; near the edge an Airy scaling takes over. This is the regime of this library, but the library proves
  upper bounds, not leading terms: the item "Asymptotic expansions" of `docs/ROADMAP.md` is open, and
  `docs/design/leading-term.md` has draft statements only (two variables, constant not explicit).
- *The Hawking-Page transition at weak coupling* (hexagon:2611.00175v1): no oscillatory-integral estimate is used.

What the lead could not confirm: the announcement says that the results of the first preprint were verified in
Lean; the preprint does not mention Lean and its listed source is one TeX file. Both preprints were written with a
model of the same family as every lead, prover and referee of this repository, so nothing in them counts here as
independent evidence. The server was unknown to the lead; the deposits are not peer reviewed.

## Decision 1: v0.7.0 is left as stamped

The release candidate (replay of record on 2113b54, stamp `stamps/20261119T213636Z-1aa26b0f21a7`, branch head
66a88bc) is not changed: no reference to the preprints and no file of the next batch enters it.

## Decision 2: the next batch, and where it lives

The next batch is the one-variable stationary-phase leading term with an explicit remainder (working label SPL),
with the two-saddle form that is uniform toward a fold as its later stage. It is developed on the branch
`claude/batch-sp-leading-term`, created from 66a88bc, pushed, with no pull request; the release branch stays as it
is, and the batch is rebased onto `main` after the owner has published v0.7.0. Every rule of `CONTRIBUTING.md`
applies from the first step (prior-art gate, registration, freeze, blind review before any Lean proof).
