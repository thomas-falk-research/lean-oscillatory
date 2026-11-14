# Answers to the external R4 research packet (W1: batch LS proof drafts; W2: explicit constants), 2026-11-14

Subject: three archives from the same external reviewer as `review/2026-11-13-external-R3-answers.md`, written against
c7cc11d in answer to the lead's brief R4. The archives, the brief and the chat are not recorded (owner privacy rule,
lessons 46). Each claim is restated in the lead's words, with the evidence the lead produced. Written by the session-11
lead.

## Summary

- **Integrity: PASS.** All three archive digests match the relayed list. All 148 manifest entries match, with no file
  missing and none unlisted. Archive 2 binds Archive 3 correctly.
- **W1, batch LS: the four frozen statements now have Lean proofs that pass the kernel.**
  - **As shipped, none of the ten drafts compiled.** Six could be compiled on their own and failed. The other four were
    blocked by their imports.
  - **The repair was mechanical.** The lead's two proof agents made them elaborate with 32 changes in all:
    - API names and deprecations;
    - rewrite forms and explicit `simp` sets;
    - one coercion, one missing parenthesis and one instance-path workaround.

    There was no change of route, statement or lemma, and nothing was found false. `LatticeGroupUnique` and the final
    file compiled unchanged.
  - **Checked by the lead in one fresh build:**
    - the four final theorems have exactly the frozen statement types;
    - their axioms are only `propext`, `Classical.choice` and `Quot.sound`;
    - per-module `leanchecker` accepts all ten modules, with negative controls showing the replay reads these builds;
    - the guard tokens are clean.
  - **Integrated in this commit.** It is not yet "machine-checked as stated": that needs the isolated replay with
    comparator-LS (CONTRIBUTING step 9) and the post-proof reviews (step 10).
- **W2, explicit constants: TRUE as hand mathematics; one sharp special case; the general problem stays open.** Two
  fresh-context referees found no BLOCKER or MAJOR finding.
  - **(Q), exactly quadratic phases:** |I| ≤ π√(‖A‖₂‖ΔA‖₂)/(m√η).
    - It is classical in kind; Hörmander's Lemma 7.7.3 is the template.
    - Its constant π is sharp. A Gaussian reaches 0.9488 of it, and no admissible amplitude exceeds it.
    - On the packet's saddle benchmark the bound is within a factor 1.152 of the integral.
  - **(L6), local:** the repository's own core argument with sharper bookkeeping. Under the repository's hypotheses it
    is uniformly smaller than `Core.lean`'s explicit constant, by a factor of about 10 or more in 200,000 sampled
    parameter sets.
  - **(L1):** correct and sharp.
  - **(G), the general one-phase bound:** correct, but useless at realistic parameters. On the packet's saddle it first
    beats the trivial bound at m ≈ 7.7·10¹⁰; the packet says so itself.
  - **The draft Lean statements** failed to parse only because they use `λ` as a variable name. The error was copied
    from the repository's own sketch in `docs/constants.md`, which is corrected here. After the rename they elaborate.
- **Not attempted, as the packet says:** W3–W6 and the moonshot appendix. No census model was used.

## What arrived

- **Archive 1, overview** (SHA-256 0831ea267d270034252241f53ccb6a6ebc8daa4b3b53cdfabbf0e7e55c0c941e): readiness ledger,
  claims register (29 entries), prior-art and query logs, disclosure.
- **Archive 2, statements** (81b46855eb4d1d6fa118a888addbf35abd764883b6c8f56052ebe316dff4cbad):
  - the W1 interfaces and controls;
  - the W2 statements, controls, measurements and thresholds;
  - a definition-only Lean file for W2 and unexecuted `#check` lists;
  - six numerical programs with expected outputs;
  - the SHA-256 of Archive 3.
- **Archive 3, proofs** (6acdfc63fdb58b56b96c2a0749e51db07741ee968b2ea4eedde1f9b6ad6d60c1):
  - ten W1 Lean files (nine parts and a final file) with hand proofs and risk registers;
  - the W2 hand proofs;
  - same-model audits.
- **The packet's own framing.**
  - Its status is PARTIAL.
  - Every Lean file is labelled UNELABORATED.
  - The W2 Lean sanity theorems are missing.
  - It makes no novelty claim and names no consumer.
  - Its strongest recommendation is "candidate for statement review".
- **AI-use disclosure.** The packet was produced with ChatGPT (exposed model name GPT-6 Astra Pro), four instances, as
  it states. Its audits are by the same model family. The lead has not verified the version.

## What the lead did

1. **Integrity.**
   - Computed the three archive digests and compared them with the relayed list.
   - Checked every manifest entry with the lead's own code.
   - Checked the Archive 3 digest recorded in Archive 2.
   - Found that `main` had moved to cb2f648 (pins PR #14 merged). This branch was brought up to date with it.
2. **The packet's programs.**
   - Read first: standard library and pinned mpmath only, with no subprocess, network, `eval` or `exec`.
   - Run on a copy in a sandbox with no network (`bwrap --unshare-all`), Python 3.13.18. The W2 grid took 284 s.
   - All exit 0. All outputs are identical to the expected files except the recorded Python version, which the
     packet's own comparison ignores.
3. **Lean, W2 statements.**
   - As shipped, the file fails to parse: `λ` is used as a binder name, and `λ` is a Lean keyword.
   - With `λ` renamed to `lam` (the lead's diagnostic copy), all five definitions elaborate.
4. **Lean, W1 proofs.** Each file was compiled at its intended module path, from a scratch tree outside the repository
   (lessons 42), at Lean v4.35.0 and Mathlib 56a0058.
   - **As shipped:**

     | File | Result |
     |---|---|
     | `Op` | 4 errors |
     | `Exp` | 1 error |
     | `Stencil` | 6 errors |
     | `FourierStencil` | 3 errors |
     | `Bound` | 1 error |
     | `Envelope` | 1 error |
     | `Unique`, `Series`, `Conv`, `Final` | blocked by their imports |

     The errors were:
     - an unbound index from a missing parenthesis;
     - `rw` patterns that did not match;
     - an argument-order mix-up between `add_le_add_left` and `add_le_add_right`;
     - a `simp` stuck on the `lp` coercion;
     - deprecated names;
     - a `change` that timed out;
     - a cast in a real power.
   - **Repair.** Two proof agents, operator side and kernel side, made the minimum changes and logged each one as
     MECHANICAL or SUBSTANTIVE:

     | Side | Changes | Mechanical | Substantive |
     |---|---|---|---|
     | Operator | 9 | 9 | 0 |
     | Kernel | 23 | 23 | 0 |

     The lead read every diff and agrees with the classification. The only change touching a definition is the
     parenthesis in the helper `lapLinear`. The original did not elaborate, the fix is its only coherent reading, and
     `LapOpFacts` forces the result to equal the frozen `latticeLaplacian`.
   - **Verification by the lead**, in one fresh scratch build of all ten files (the final file byte-identical to the
     packet's):
     - no errors and no warnings;
     - the four `OscInt.API.latticeSchrodinger…` theorems have exactly the frozen statement types (checked with
       `example`);
     - `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound` only;
     - per-module `leanchecker` accepts all ten modules;
     - two negative controls show the replay is not vacuous: a missing module is reported, and with one part's
       `.olean` removed the check of the final module fails and names the scratch file;
     - the guard-token scan is clean.
   - **Integration** (this commit):
     - the ten files are in `OscInt/Front/`, with the repository header and a provenance docstring;
     - `OscInt.API` imports the final file;
     - `StatementTypes.lean` has four new `#assert_type_is` lines;
     - `stamps/statements.json` has `proved_by` filled by `make statements`;
     - the API snippets are updated;
     - the STATUS rows, README, `docs/which-theorem.md`, `docs/prior_art.md` (AI-use disclosure) and
       `docs/proof-LS.md` are updated.
5. **The lead's own checks.** `numerics/review/r4_packet_checks.py`, record
   `numerics/results-r4-packet-checks-2026-11-14.txt`: 8/8 PASS.
   - The (Q) coefficient of the benchmark, from exact SymPy norms.
   - The saddle integrals, by a third method different from both of the packet's: exact reduction to incomplete gamma
     functions. They reproduce the packet's bound-to-integral ratios 1.1401 to 1.1513 to twelve digits.
   - (Q) on exact Gaussians with non-diagonal Hessians and linear terms: largest ratio 0.949.
   - The threshold integers.
   - (L1) on a datum.
   - The referee's MINOR-1 (below).
   - The W1 operator datum: ‖f‖² = 91 and ‖Δf‖² = 882.
   - The first run crashed on a type conversion in the lead's own code; it was fixed before the recorded run.
6. **Fresh-context agents** (Claude instances, same model family as the lead), launched at c7cc11d on a clean tree.
   Times are each agent's own `date -u`:

   | Agent | Scope | Start | Finish | Ran Lean |
   |---|---|---|---|---|
   | Proof agent, operator | `Op`, `Exp`, `Unique`, `Envelope`, `Bound` | 10:31:04Z | 10:38:07Z | yes, scratch only |
   | Proof agent, kernel | `Stencil`, `FourierStencil`, `Series`, `Conv` | 10:31:05Z | 10:38:40Z | yes, scratch only |
   | Blind statement referee | Archive 2 and the repository; barred from Archives 1 and 3; no proving | 10:33:59Z | 10:59:16Z | no |
   | W2 proof and prior-art referee | Archive 3 W2, Archive 1 prior art, web sources | 10:33:59Z | 10:43:10Z | no |

   - No referee could write a report file (harness rule), so the reports exist only in the session record.
   - The tree was not modified while any of them ran.
7. **Order.** The lead compiled the W1 drafts, which are Archive 3 material, before the blind statement referee started.
   That referee was barred from Archive 3.

## W1 verdict

**The LS proofs are correct as Lean proofs of the frozen statements, as far as build, axiom audit and per-module kernel
replay show.** The packet's hand routes follow `docs/proof-LS.md` and its referee revisions:
- the exponential series over ℂ;
- evaluation through `restrictScalars ℝ`;
- `ODE_solution_unique_univ`;
- `Summable.tsum_comm`;
- the existing box-volume lemma.

Its W1 controls were spot-checked by the blind referee and reproduce: the operator datum, stencil coefficients by walk
counts, the kernel modulus at d = 3 against Bessel products, and the envelope plants.

What remains before "machine-checked as stated":
- the isolated `make verify-all`, with all six kernels and comparator-LS against the frozen challenge;
- the post-proof reviews (A, B, adversarial);
- the records.

## W2 verdicts and findings

**(Q), exactly quadratic phase: TRUE; constant sharp.**
- The lead derived it independently: Plancherel plus a Cauchy–Schwarz split with weight a + b|ξ|⁴ gives exactly
  π/(m√η)·√(‖A‖₂‖ΔA‖₂). The bound is uniform in the linear term and the constant term.
- The proof referee re-derived it, including the damped-Gaussian justification of the Fresnel kernel, and found it
  complete.
- The blind referee showed the constant π cannot be lowered: a chirped Gaussian reaches 0.94885, and an extremal
  Fourier profile reaches 1.
- The bound is classical in kind. Evans–Zworski Theorem 3.12, step 1, gives the L¹-of-Fourier form, and Hörmander's
  Lemma 7.7.3 is the L²-derivative template. The explicit constant was not found in print. That is not evidence of
  novelty, and the packet claims none.
- Its scope is narrow: exactly quadratic phases.

**(L6), local core with explicit weights: TRUE.**
- It uses the repository's frozen van der Corput constants: 8·8 = 64 for j = 2, and 8·18 = 144 for j = 3.
- The proof referee found it the same argument as `Core.lean`, with the endpoint terms that vanish actually used,
  integrals instead of suprema, and sharper derivative factors.
- **Findings:**
  - **MINOR, the evaluated rows are loose** (blind referee; lead's check). The benchmark rows replace ‖A_XY‖₁ by the
    Cauchy–Schwarz value 5.4191, where the exact value is 4.0797. So the rows are valid but loose by a factor 1.33:
    - the saddle coefficient would be 67.42, not 89.55;
    - the first integer beating the comparator would be 69, not 92;
    - the measured ratios would be about 41 and 83, not "above 54" and "above 110".
  - **NIT.** For separable data the best possible constant is about 2.83, so 64 leaves a factor of about 22.

**(L1), local non-critical: TRUE and sharp.** The blind referee's datum reaches ratio 1.0043 at m = 512. Finding:
- **NIT.** One planted variant is weak. "Halve the U₁/c coefficient" would be a stronger control, since it is already
  false.

**(G), general one-phase S2.2: TRUE; useless at realistic parameters, as the packet says.** The proof referee checked
every step and found no gap:
- the quintic partition (derivative sums 7.5 and 31.9 against the claimed 8 and 56);
- the noncritical and critical tiles, the Schur complement and the combination of branches;
- the absence of a tile-count factor.

The s⁻² cut-off term is 99.7% of the coefficient. Findings:
- **MINOR (prior-art scope).** The η-dependence is about η^{−17/4}, worse than Alazard–Burq–Zuily's a₀^{−3} in two
  dimensions. The comparison should say so.
- **NIT.** In the non-stationary regime (G) is within a factor 2 of the integral, so "useless" holds for critical-point
  data only. The packet's wording, "on the registered saddle", is already right.

**The W2 Lean statement drafts: TRUE as written and equivalent to the prose.**
- The blind referee showed that each restriction the packet disclosed as narrowing loses nothing:
  - m ≥ 1, by homogeneity;
  - q = 0, because e^{imq} has modulus one;
  - global smoothness, by a cut-off.
- The analytic Lean sanity theorems are missing, as the packet says (lessons 33).

**Prior art.**
- The proof referee read Alazard–Burq–Zuily, arXiv:1511.01439, Theorem 1 (the packet's description is accurate) and
  Evans–Zworski, version 0.2, Theorem 3.12 (accurate).
- **MINOR.** The packet's log names Hörmander §7.7 as not accessed. It should name Lemma 7.7.3 as the classical template
  for (Q).

**Nothing in W2 restates a frozen statement.** If the owner wants explicit local constants as a batch:
- the local (L6) and (L1) theorems are the "cheap first deliverable" that `docs/constants.md` §4.6 already recommended;
- (Q) is a self-contained candidate.

Each would need the full statement-first procedure: the analytic Lean sanity layer the packet lacks, a freeze, and blind
review. Recorded as a ROADMAP candidate.

## Corrections to this repository

1. **`docs/constants.md` §4.2.** Its Lean statement sketch used `λ` as a binder name, which does not parse; the R4 draft
   copied it. The binder is now `lam`, with a dated note.
2. **`docs/constants.md`.** The dependency diagram cited `Core.lean:923–945` for the core constant; `coreEstimate` is at
   930–952 (blind referee, NIT). Corrected.
3. **`docs/HANDOFF.md`.** "Start here" said PR #14 still needed its pin fix. It was merged (cb2f648). Updated.

## Process notes

- The proof agents ran Lean while the two referees were reading. This is allowed: the referees did not run Lean, and no
  replay was running (lessons 28, 49).
- No referee ran while the tree changed. The tree was modified only after the last referee finished (10:59:16Z).
- **The compile harness.** Lean resolves a package from the first search-path entry that has an `OscInt/` directory. A
  scratch build must therefore mirror the repository's built modules into a directory placed first on the path. The
  lead's first attempt, with the scratch output last, failed on the imports between parts. That was a harness error,
  not a packet defect.

## Addendum: the W2 formal sanity layer (2026-11-14, relayed by the owner)

**What arrived.** A follow-up from the same reviewer, supplying the analytic Lean sanity layer that the R4 packet lacked:
- two archives;
- `oscint-w2-sanity-proofs-2026-11-14.zip`, SHA-256 42c3c90113ac30dd6692c76cd3d2b76b577a268ee4c55f75ac7c97ee7dab05c6;
- `oscint-w2-sanity-statements-2026-11-14.zip`, SHA-256 819814601e0a6824a63bde7ebb86e4f9c2397ed3124de69f9552035527d82eeb;
- a checksum list naming a third, audit archive, which was not relayed.

Both relayed archives match the list. All 37 manifest entries match, and the statements archive binds the proofs
archive.

**What it contains.** Seven Lean modules (`OscInt.R4Sanity.*`, 1,861 lines):
- the R4 W2 statement file, byte-identical to the original apart from `λ` renamed to `lam`;
- eight conditional sanity theorems. Each takes one W2 statement as its only hypothesis, discharges every analytic
  premise on a concrete datum, and proves that the instantiated right side is below 1/4 ≤ ∫|A|:
  - L6 in both forms, saddle and fold;
  - L1 with genuine directional curvature;
  - (G) once in each branch: a determinant-only datum and a gradient-only datum;
  - (Q) with a non-diagonal Hessian;
- fifteen input-premise controls.

**What the lead did.**
- **The numerical programs**, run on copies in a sandbox with no network: all pass, with outputs matching the expected
  files apart from runtime fields.
- **The lead's own check** (mpmath, the lead's code):
  - ∫|A| = 5.9429, inside the packet's enclosure;
  - A(0) = 699/119 + 223/119·i;
  - the quadratic right side at m = 65536 is 1.56·10⁻⁴, below its cap 25/1024.
- **Lean, as shipped:** `W2Statements` compiles. `Amplitude` (15 errors) and `Phases` (7) fail, and the other four are
  blocked by their imports.
- **Repair.** Two proof agents changed only proof bodies:

  | Module | Changes | Mechanical |
  |---|---|---|
  | `Amplitude` | 12 | 12 |
  | `Bounds` | 4 | 4 |
  | `Arithmetic` | 1 | 1 |
  | `Phases` | 7 | 7 |

  - Typical fixes:
    - a `using` clause mis-indented under its `simpa`;
    - `convert` replaced by `congr_deriv`;
    - `ext` splitting into two goals;
    - a missing `fun_prop` rule for the real-to-complex coercion;
    - `Set.Icc_prod_Icc` firing too early.
  - Nothing found false. No statement, datum or constant changed.
  - `Sanity` and `Controls` compiled unchanged.
- **Verified by the lead in one fresh scratch build of all seven modules:**
  - no errors; the only warnings are eight linter notes in `Phases`, on untouched lines;
  - each of the eight final theorems has exactly one premise, its W2 statement (eight arrows in all);
  - `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound` only;
  - per-module `leanchecker` accepts all seven modules;
  - the guard-token scan is clean.

**Verdict.** The W2 candidate statements now have machine-checked conditional sanity: each statement's hypotheses are
satisfiable on a nontrivial datum where the bound beats the trivial one (lessons 33, 47). This is not a proof of any W2
estimate. Nothing is integrated into the library, because W2 is not frozen; the sources stay outside the tree.

**Limits,** stated by the packet and confirmed by the lead:
- The local data have zero transverse third and fourth derivatives, so deleting those hypotheses would go undetected.
- The ten planted false variants have no compiled planted copies. Their falsity rests on the earlier numerical and
  referee evidence (lessons 44: a compile failure is not semantic evidence).
- The caps are generous, by a factor of about 150 for (Q), and say nothing about usefulness.

For a future W2 batch this layer is the starting point. The freeze would still need its own planted copies, recorded
(lessons 33).

## AI-use disclosure

- The proof drafts and the W2 mathematics were produced with ChatGPT (GPT-6 Astra Pro), as the packet states.
- The lead, both proof agents and both referees are Claude instances. Agreement between them is not independent
  confirmation.
- The machine checks are the kernel's. The fidelity readings are AI only, with no human reviewer yet.
