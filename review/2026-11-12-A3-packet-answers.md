# Answers to the external A3 packet (Lean proofs of S1.k, S5.1, S5.1′), 2026-11-12

Subject: one packet from the same external reviewer as `review/2026-11-12-DNLS-packet-answers.md`. It answers the
lead's third research prompt, which asked for batch A3 only: the frozen statements S1.k (`VdCkStatement`), S5.1
(`CuspBoundStatement`) and S5.1′ (`CuspBoundGenStatement`), whose comparator was the one gap in every replay. It was
written against 9dcbf0c.
- The packet, the prompt and the chat are not recorded (owner privacy rule, lessons 46).
- Each claim is restated below in the lead's words.
- Written by the session-10 lead. This file is first committed with the integration commit. The replay and the
  post-proof reviews are added when they exist.

## What arrived

**Lean files.** Seven modules, labelled by the reviewer "compile-ready, uncompiled": its environment could not
download Lean (HTTP 403).
- `OscInt/Cusp/VdC4.lean` (P1);
- `OscInt/Cusp/Core4.lean` (P2);
- `OscInt/Cusp/Implicit4.lean` (P3);
- `OscInt/Cusp/Transverse.lean` (P4);
- `OscInt/Cusp/Normalize.lean` (P5);
- `OscInt/Cusp/VdCk.lean` (S1.k for every k ≥ 2);
- `OscInt/Cusp/Final.lean`.

**Also in the packet:**
- hand proofs of each part;
- a patch adding the imports and the type assertions;
- name audits against the pinned sources;
- a prior-art record;
- falsification examples;
- a verifier.

**Hand-proof constants:**
- the P2 core constant 304 ν^{−1/4} μ^{−1/2}(1 + 4b)[1 + 2a(1 + 24β⁶)], with β = max{1, D, μ^{−1}};
- the P4 constant 4ab(1/c + D/c²);
- S1.k by induction with the radius μ^{−1/(k+1)}.

## What the lead did

1. **Integrity.** The archive's SHA-256, cca17e47309c2598036526c25a4a95ade9dba303b54cf4fe20142428d9770a76, matches
   the one the owner relayed.
   - Times (UTC, file times in the session scratchpad; added after the adversarial review,
     `review/2026-11-12-A3-post-proof-answers.md`, MINOR 6): extraction 22:38:56; compilation in the worktree
     22:42:36 to 22:52:19; integration commit 93a8a8d 23:02:13.
   - The owner approved compilation before the first compile.
2. **Safety scan before running anything.** The lead read every Lean file in the packet for constructs that execute
   code at elaboration or weaken the proof. Searched for:
   - code execution: `#eval`, IO, `run_cmd`, `initialize`, macros, `elab`, `unsafe`, `extern`;
   - weakening: `sorry`, `admit`, `axiom`, `native_decide`.
   
   None was found. The only `elab` is the repository's own `#assert_type_is` in `StatementTypes.lean`.
   - The patch changes existing files only by adding two `import OscInt.Cusp.Final` lines and the type assertions.
   - The new definitions are helpers in auxiliary namespaces: their own, except that the P3 helpers extend the
     existing `OscInt.StationaryPhase.ImplicitAux`. Nothing frozen is redefined or shadowed.
   - The session's safety filter blocks running external code by default. The owner approved compiling this packet
     on 2026-11-12, on the condition of an isolated worktree first.
3. **Compilation, in an isolated git worktree at 100d545 with the patch applied:**
   - **First pass:** P1 and P4 compiled with no errors and no warnings. VdCk had two errors; P3 had one error (P5
     failed only through its import of P3); P2 had two errors.
   - **Five elaboration fixes by the lead.** None changes a statement, a hypothesis or the mathematics:
     - `VdCk.lean`: twice, a cast `((1 + 1 : ℕ) : ℝ)` or `((2 + 1 : ℕ) : ℝ)` is rewritten to the numeral before an
       existing step. This replaces a `simp` that made no progress.
     - `Implicit4.lean`: a trailing `ring` after a `simp` that had already closed the goal is removed.
       (The removed `ring` cannot be seen in the integrated file; the other four fixes can.)
     - `Core4.lean`: a `show` states the goal with the local `g` before a rewrite, because the goal was not
       beta-reduced.
     - `Core4.lean`: `oscInt2_eq_iterated` is given its phase explicitly, `(Q := fun k => Q k + p * k.1)`, because
       elaboration had chosen the pointwise sum of functions.
   - **After the fixes:**
     - `lake build OscInt` succeeds;
     - `StatementTypes.lean` prints TYPE-OK for `OscInt.API.vdCk`, `cuspBoundGen` and `cuspBound` against the frozen
       statement types;
     - `#print axioms` on all 51 new theorems (there are also 10 new definitions) shows only propext, Classical.choice
       and Quot.sound;
     - the guard passes, with no `sorry` and no banned constructs;
     - `make lean` (build, guard, axiom audit) passes in the worktree.
   - **The comparator did not run in the worktree.** Lake treated the symlinked package directory as missing, which
     is an artefact of the setup, not of the proof. It runs in the main tree's `make verify-all`.
4. **Integration into the main tree (this commit):**
   - the seven files, with the lead's five fixes;
   - the headers rewritten: the "uncompiled" notes are removed, the copyright follows repository practice (the van
     der Corput files keep J. Roos's line, as the files they extend do), and a provenance note is added;
   - the two imports and three `#assert_type_is` lines (API names);
   - `stamps/statements.json` regenerated (`proved_by` set);
   - API annotations switched to type snippets;
   - STATUS rows set to "machine-checked by build …; full replay and post-proof reviews pending".

## The route and the deviations

The route (`docs/proof-A3.md`) was refereed at b719ba4, before these parts existed. It covers the cusp parts P1–P5;
S1.k for general k is outside it (correction after the adversarial review, MAJOR 2). The cusp parts follow it, with one
deviation:
- **P4.** It integrates by parts against the whole compactly supported amplitude in the transverse variable, rather
  than first cutting the inner integral to [−b, b] as the route revision proposed.
- It needs only |∂_yΦ| ≥ c and |∂²_yΦ| ≤ D on the box, and no bound in the x-direction, so any linear term p·x is
  allowed.
- The Lean proof compiles against the frozen `TransverseNonStatFacts`. Whether this route is the simplest one is a
  question for the post-proof review.

## What is not yet checked

- **The full replay.** `make verify-all` on the integration commit, including comparator-A3 against the frozen
  challenge and the per-module kernel replay, is to be run next.
- **The post-proof reviews.** Two fresh-context referees (fidelity and mathematics) and an adversarial referee are to
  read the parts.
- **The packet's falsification examples, not yet checked by the lead.** For example, the phase (y + x²/2)², whose raw
  quartic is nonzero but whose reduced quartic vanishes, and the family x⁴ + ((1 + x)/2)y² + qy, whose reduced fourth
  derivative 24 − 12q² vanishes at q = √2. The post-proof referees will check them.
- **The prior art.** The packet records:
  - Roos–Praveen: the S1.k constant, with smooth hypotheses;
  - Ikromov–Müller and Borovyk–Goldberg: the 3/4 cusp exponent, with C³ amplitudes;
  - Greenblatt 2025: C¹ amplitudes, but below the 3/4 exponent.
  
  It says that the original Duistermaat and Varchenko papers were inaccessible. The lead has not re-read these. The
  novelty wording stays "machine-checked; the mathematics classical; C² amplitudes with uniformity in the linear term
  not found in the logged search" until the post-proof review.

## AI-use disclosure

- **The proof text** of these parts was drafted with an OpenAI model (the reviewer's tool; version not stated for this
  packet). The cusp parts follow the route written and refereed by Claude instances; S1.k for general k had no route
  review (`docs/proof-A3.md` lists it under "Not needed"), only the post-proof reviews.
- **Its integration, the fixes and the checks** were done by the lead, a Claude instance.
- Agreement between instances of one model family is not independent confirmation. The Lean kernel check is.
- `docs/prior_art.md` records this disclosure for batch A3.
