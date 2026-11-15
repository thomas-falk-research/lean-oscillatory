# The external research packet behind batch D4U (2026-11-15): what it contained, and what the lead did with it

Written by the session-12 lead after the adversarial post-proof referee of batch D4U (finding 1) asked for a record of
the work that preceded the freeze. In the lead's words (lessons 46); the packet itself is not in the repository.

## The packet

A research packet produced with an OpenAI model at the owner's request (version not stated in the packet) for the
downstream project that uses OscInt for split-step quantum walks, received by the lead on 2026-11-15 at 11:00:11 UTC
(time of the uploaded archive). Of its parts, one concerns OscInt: a uniform form of the D4 limit S4.2, needed
downstream for the sharpness of the t^{−2/3} rate along lattice sites whose offset from the moving D4 point stays
bounded. For it the packet supplied:
- a hand proof that the D4 limit holds uniformly over totally bounded C² families of amplitudes and over bounded linear
  offsets, from S4.1′ and S4.2: a common radius, the uniform bound on differences, a finite net, and the modulation
  family for the offsets;
- unelaborated Lean drafts: statement files for both forms, a sanity file, and a blueprint file with three parts named
  `CommonRadiusFacts`, `FiniteNetFacts` and `ModulationFacts` and two reduction theorems from those parts to the two
  statements.

## What the lead did with it, before the freeze

- 11:00–11:06 UTC (about): a fresh-context referee of the lead checked the hand proof against the stamped S4.1′, S4.2
  and the definitions `AmpBound`, `oscInt2`: verdict CORRECT, with two minor findings (an informal remark about
  translated D4 points, and a heuristic presented as a necessity check) and four nits (among them that a positivity
  requirement in a blueprint part could be avoided). It ran its own derivative-norm and quadrature checks; run time
  308.8 s by the session's task record, its check scripts dated 11:04:46–11:05:23. Its report is not recorded
  (lessons 46); this is the lead's summary.
- 11:03:44–11:13:33 UTC: the lead elaborated the packet's Lean drafts in a scratch directory outside this repository,
  against the built library, to assess them. The statement and sanity drafts elaborated; the blueprint draft elaborated
  after a scratch-only module-path fix, including its two reduction theorems (so a Lean reduction of statements of this
  kind to S4.1′ and S4.2 existed, and had been compiled by the lead, before the freeze).

## How batch D4U relates to it

- **Statements.** Written fresh by the lead after that assessment (first committed in 5bf645a at 11:50:11 UTC, the file
  unchanged since; statements commit 33c56db at 12:07:20, stamped at 12:29): the same two forms,
  with the lead's own definitions (`D4LimitPhase`, `AmpTotallyBounded` with a finite subset as the net, the max-norm
  bound on offsets, no `T ≥ 1`).
- **Route.** `docs/proof-D4U.md` follows the packet's decomposition: the part names `CommonRadiusFacts` and
  `ModulationFacts` are the packet's, and the ε/2 net argument is the packet's mechanism (and the classical one). The
  lead's changes: `LinearFacts` (subtractivity of the integral) in place of the packet's `FiniteNetFacts`, with the net
  argument moved into the assembly; the compactness argument for the modulation family through joint smoothness and the
  slice lemma of C10.
- **Lean proofs.** The assembly, P-radius and P-linear were written by the lead and P-mod by a proof agent of the lead,
  after the reviews were answered and stamped; none of the packet's Lean was copied into the repository.
- **The claim this supports.** The statements were frozen, stamped and blind-reviewed before any Lean proof entered the
  repository, and the reviewers were not shown the packet. The batch does not claim that its proof was found
  independently of the packet, nor that no proof (on paper or in scratch Lean) existed before the freeze.
