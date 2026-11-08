7218811ebd (`git rev-parse HEAD` = 7218811…, "LE post-proof and adversarial referee prompts")

# Post-proof referee B, batch LE (T0E, T6F, T6E)

**Verdict.** All three theorems are FAITHFUL at full scope. I found no BLOCKER and no MAJOR. There are three MINOR findings and three NITs. Two of the MINORs are about documentation and order evidence; one is about non-vacuity.

I wrote only in /tmp/postB/ (Check.lean, Deps.lean). I ran one Lean process at a time under `nice -n 10`, never ran make or lake build, and wrote nothing in the repository.

## (1) Types are exactly the frozen constants
- **Stamp.** SHA-256 of `OscInt/Statements/LatticeExplicit.lean` at HEAD is `c2016339…b921`. That equals its line in `stamps/20261108T160847Z-4a183530559f/manifest.txt` (commit 4a18353).
  - `Statements/Global.lean` (where `latticeKernel` and `torusBox` live), `Statements/VanDerCorput.lean`, `Challenge/LatticeExplicit.lean` and `comparator-LE.json` also match the manifest.
  - Only two reviewed files changed since the stamp: `LatticeExplicitSanity.lean` and `docs/statements.md`. Both changed in c91a9a8, before the proof commit, with no statement text changed.
- **Types.** `StatementTypes.lean:73-75` asserts syntactic `Expr` equality with the three constants. The replay `docs/replay/2026-11-08-session7-LE-verify-all.txt` shows:
  - TYPE-OK at lines 123-125;
  - commitments matching the stamp at lines 332, 339 and 341;
  - `comparator-LE.json` accepted by six kernels at lines 439-461.
- **No Lean change after the replay.** `git diff a1d2a64 HEAD` touches only the replay record and the two prompts.
- **Axioms.** My own `#print axioms` on all three gives only propext, Classical.choice and Quot.sound.

## (2) Fidelity to docs/statements.md ("Batch LE", clarifications 6–9)
- **T0E: FAITHFUL, full scope.**
  - `latticeKernel1` is the oriented interval integral over [−π, π] of exp(i(t cos k + ξk)), and the norm is the complex modulus.
  - The statement is ∀ t ξ real with 0 < t. The right side is 24·2^{1/4}·t^{−1/2} + 36·2^{1/6}·t^{−1/3}; `-(1:ℝ)/2` parses as −1/2.
  - I restated T0E from the docs in my own form (√√2/√t, exp(I·…), −(1/3)) and derived it from `OscInt.API.latticeKernel1Explicit`. It compiles (/tmp/postB/Check.lean).
- **T6F: FAITHFUL, full scope.** It holds for all real t and x ∈ ℤ². `latticeKernel` is the unchanged GD kernel over `torusBox = Icc ×ˢ Icc`. My restatement with the box spelled out compiles against it.
- **T6E: FAITHFUL, full scope.**
  - It holds for t ≥ 1, uniformly in x, with constant (A+B)². I compiled a derived corollary |K| ≤ 4761·t^{−2/3} from it plus `latticeConst_bounds`.
  - Clarification 8 notes that T6E is also true for 0 < t; this is disclosed, not a fidelity issue.
- **Clarification numbers.** I recomputed them: A = 28.5410, B = 40.4086, (A+B)² = 4754.05; T0E beats 2π for t > 518.525; T6E beats 4π² for t > 1321.47; the user normalisation gives 75.86. All agree with the docs.

## (3) Non-vacuity
- The hypotheses (0 < t, 1 ≤ t) are clearly satisfiable.
- `LatticeExplicitSanity.lean` discharges them on closed data (t = 8, 1/8, 3, −2, 1, and the diagonal). But every theorem there is **conditional**: `(h : …Statement) → …`.
- In the tree, no compiled file applies these theorems to the proved theorems. Grep finds only bare type ascriptions in `examples/api/Snippets.lean:192-200`; there is no LE consumer, unlike GD's `ConsumerLattice`.
- I applied all six conditional sanity theorems to the proved theorems in scratch, and they compile.

## (4) What the proofs rest on
I took the transitive closure of `OscInt.*` constants used by the three proofs, stopping at the S1 theorems (/tmp/postB/Deps.lean). It contains only:
- the frozen statement definitions: `latticeKernel1`, `latticeKernel`, `torusBox`, `oscInt`, `ampNorm`, `HasDerivOn`, `AmplitudeOn`, and the three statement constants;
- `OscInt.vanDerCorput_two` and `OscInt.vanDerCorput_three`, which are TYPE-OK against `VdC2Statement`/`VdC3Statement` (replay lines 79-80);
- `Statements.sanity_amplitude_one`, a proved lemma in the frozen and stamped statement file;
- the blueprint propositions `LEAngleFacts`, `LEPiece2Facts` and `LEPiece3Facts`, plus local lemmas. The blueprint propositions are hypotheses that are discharged, so they do not affect what is proved.

No unreviewed internal statement matters. The parts instantiate S1.2 with μ = t·2^{−1/2}, ψ = 1, p = ξ (`LatticeExplicitParts.lean:61-80`) and S1.3 likewise (lines 83-97), as the docs' route says. The oleans are newer than their sources.

## (5) Documentation and order claims against the evidence
- **The route-review order was not kept, and this is disclosed truthfully.** `docs/proof-LE.md` ("Revision after the route referee", M1) and `docs/lessons.md` item 42 say so. The evidence agrees:
  - the route referee saw untracked part files dated 16:57 after HEAD 240455c (16:55);
  - the referee report was committed together with the proofs in a1d2a64;
  - the file mtimes are Parts 16:57:11 and Final 16:57:29.
- **"Statements frozen and blind-reviewed before any proof" is supported only partly; see MINOR-3.**

## Findings

**BLOCKER:** none.

**MAJOR:** none.

**MINOR-1 (non-vacuity is not exercised in the tree).** `OscInt/Front/LatticeExplicitSanity.lean:55-101` are all conditional on `h : …Statement`, and nothing in the build applies them to `OscInt.API.latticeKernel1Explicit`, `latticeKernelFactor` or `latticeLaplacianExplicit`. `examples/api/Snippets.lean:192-200` only restates the types. I compiled the six instantiations in scratch and they work.
- Fix: add them, for example in an `examples/consumer` file or at the end of `LatticeExplicitFinal.lean`.

**MINOR-2 (STATUS and README not updated for LE).** `docs/STATUS.md` has no LE rows and no session-7 LE paragraph. `README.md`'s statement table (line 36 area) has no LE row either.
- The pre-proof answers (`review/2026-11-08-LE-pre-proof-answers.md`, Referee A MAJOR) promised that "the STATUS rows will carry 'owner decision pending'". Today only `stamps/statements.json:503-535`, `docs/api.json` and the annotations record LE as proved.
- This is an omission, not a false claim. Presumably it is due after the post-proof reviews, but the promise is open.

**MINOR-3 (strength of the "before any proof existed" wording).** `docs/proof-LE.md` (M1 paragraph) says the statements were stamped (16:08:50Z) and the reviews were stamped (16:45:19Z) "before any proof of an LE statement existed".
- The RFC 3161 stamps prove that the statements and reviews existed by those times. They cannot prove that no proof existed earlier.
- The route/assembly commit 240455c and the proof commit a1d2a64 are not stamped. Their times are self-reported git dates. The referee's 16:58 observation and the file mtimes corroborate the order but are not external evidence.
- The API3 paragraph in `docs/STATUS.md` uses the honest qualifier "that none existed in scratch rests on the lead's statement". The LE text should carry the same qualifier.
- No evidence contradicts the claimed order.

**NIT-1.** The first paragraph of `docs/proof-LE.md` still says the name checks are in `/tmp/lead/Names.lean` with "output in the commit message". The m2 fix later moved them to `MathlibNames.lean` (for example lines 67 and 72), but the opening sentence was not updated.

**NIT-2.** The `LatticeExplicitAssembly.lean` docstring says "compiled before any part was proved". `t6e_of` is already a complete conditional proof of T6E from T0E and T6F. It was committed after the review stamp, so the order is fine, but "no proof of an LE statement before 240455c" would be more exact than "before any part".

**NIT-3.** Clarification 8 suggests a `0 < t` corollary of T6E, and the answers say it "may be added with the proofs". It was not added. That is optional and needs no action unless downstream wants it.

## Summary table
| Theorem | Type = frozen constant | Verdict | Scope | Used on data (compiled) | Rests on |
|---|---|---|---|---|---|
| T0E `latticeKernel1Explicit` | yes (TYPE-OK, commitment, comparator, stamp SHA) | FAITHFUL | full | conditional sanity only; instantiated in my scratch | S1.2, S1.3, Mathlib |
| T6F `latticeKernelFactor` | yes | FAITHFUL | full | same | Mathlib (Fubini) |
| T6E `latticeLaplacianExplicit` | yes | FAITHFUL | full | same | T0E, T6F, Mathlib |

Scratch files: /tmp/postB/Check.lean (axioms, the six sanity instantiations, independent restatements of T0E/T6F, the 4761 corollary) and /tmp/postB/Deps.lean (dependency closure).
