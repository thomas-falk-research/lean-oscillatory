# Lessons

One durable lesson per entry: what happened, why it mattered, the rule. Rules that can be checks are checks
(named after "Check:"). Read at the start of every session.

## 1. The brief's Mathlib names were wrong at the pin (2026-11-05)
`exists_smooth_zero_one_of_isClosed`, `fourierIntegral_gaussian_pi` and the import `Mathlib.Data.Real.Basic` do not
exist or are deprecated at Mathlib `56a0058`. A plan built on remembered names fails late, inside a proof agent.
Rule: every Mathlib name the plan or docs rely on is `#check`ed at the pin. Check: `MathlibNames.lean`, run by
`make lean`.

## 2. A bundled checker reported a problem and exited 0 (2026-11-05)
`lake env lean4lean OscInt.Basic` printed "found a problem … incompatible header" with exit status 0.
Rule: a checker's verdict is its acceptance line, never its exit status alone. Check: `replay` `verdict()` (unit
tests include this exact output).

## 3. The axiom audit passed a proof of `1 = 2` (2026-11-05)
A metaprogram added an ill-typed theorem under `debug.skipKernelTC`; `lake build` succeeded and `#print axioms`
reported no axioms. Only kernel replays rejected it (all seven). Rule: the axiom audit never stands alone; every
push runs the replay. Check: CI `verify-all` includes `lean-replay`; guard forbids `run_cmd`, `elab`,
`debug.skipKernelTC`.

## 4. `leanexport` shares subterms up to alpha-equivalence and binder annotations (2026-11-05)
The first commitment format included binder names; environment and export disagreed on 138 656 lines, all binder
names, binder annotations or `let` flags. Rule: a commitment covers only what both producers determine; say what is
not covered. Check: `canon.rs` test `binder_names_and_annotations_are_ignored_body_is_not`; `make commit` compares
producers byte for byte.

## 5. Stale `.olean` files are replayed (2026-11-05)
After deleting a negative-control module, `leanchecker OscInt` still checked its `.olean` and failed. The reverse
risk is worse: a replay that silently covers files no longer in the sources. Rule: replay runs only on a build
directory whose `OscInt` oleans all have sources. Check: replay step "no stale build products".

## 6. `leanchecker --from-export` accepts an empty export (2026-11-05)
An export command that failed produced an empty file, which the checker accepted. Rule: before any checker runs,
the export must contain every audited theorem as a theorem and only permitted axioms. Check: replay
`check_export()`.

## 7. `verify-all` rebuilds three times (2026-11-05)
`lean-replay` and `commit` each depend on `lean`, so one `verify-all` runs the build and the audit three times
(about 5 s each with a warm cache). Harmless now; with a large library it will cost minutes. Rule: when the build
exceeds a minute, make the audit outputs file targets so make skips repeats. No check yet (a timing, not a rule).

## 8. The comparator's required-constant list was wrong from memory (2026-11-05)
The list of constants `challenge` adds to the challenge export was written from memory; the comparator's own
`Exporting #[…]` line showed eight missing and seven superfluous. Caught by running `lake comparator` before any
proof existed (it rejected, as it must, with no solution). Rule: any list another tool dictates is copied from that
tool's output, with the date and version. Check: none automatic; the stamp records the challenge export hash, so a
later list change shows as a hash mismatch in `make comparator`.

## 9. CI was red for six pushes and I did not look (2026-11-05)
After the S1 stamp every CI run failed: (a) `comparator` correctly rejected because no proof existed yet, an
expected failure that (b) masked a real one, `stamp-verify` failing on CI's shallow checkout (the stamped commit was
absent). Both were found only when checking CI at the end of M1. Rules: an expected "not yet" is SKIPPED, never FAIL
(`challenge check` exits 3 when no challenge theorem is declared, fails on a partial solution); CI checks out full
history (`fetch-depth: 0`); after every push, read the CI result before the next claim. Check: the first two are
code (`tools/src/bin/challenge.rs`, `.github/workflows/ci.yml`); the third is a process rule with no automatic check.

## 10. Stamped commitments were recorded but never enforced (2026-11-05)
The adversarial review found that `make commit` only compared the two producers with each other and `make comparator`
judged against the newest stamp, so an edited statement plus a fresh stamp would have passed silently. Rule: a
freeze is a pin that a check enforces, not a file that exists. Check: `stamps/pins.txt`, enforced by `make commit`
(commitments and statement-file hashes against the pinned stamp) and by `make comparator` (pinned challenge stamp);
negative control recorded in `review/2026-11-05-S1-adversarial.md`.

## 11. Calibration round 1: the referee caught 4/4 planted errors, and two controls passed (2026-11-05)
Why it mattered: it is the first evidence that a FAITHFUL verdict means something (interval [0.40, 1], small n).
The reports also showed that a sanity theorem restating a hypothesis in its own words tests the restatement, not
the statement. Rule: hypotheses are bundled as named `def`s used by both the statement and its sanity theorem.
Check: none automatic yet (a lexical check that each sanity theorem mentions the statement's hypothesis defs is
possible once S2's statements exist).

## 12. `ContDiff ℝ ⊤` means analytic in this Mathlib (2026-11-05)
The S2/S3 infrastructure blueprint wrote `ContDiff ℝ ⊤` for "smooth". At Mathlib 56a0058 the smoothness index is
`WithTop ℕ∞`, so `⊤ = ω` (analytic); a compactly supported analytic function on ℝ² is zero, which made the partition
of unity part false and the cut-off part vacuous. Proof agent G3 found it by proving `¬ PartitionFacts` instead of
weakening it (rule 3 of the briefs worked). Rule: write `∞` (with `open scoped ContDiff`) for C^∞, or a numeral.
Check: guard rejects `ContDiff…`, `ContDiffOn…` followed by `⊤` (tests in `guard.rs`).

## 13. Structure projections are theorems the guard cannot count (2026-11-06)
A helper `structure` with `Prop` fields (agent H2) adds one projection theorem per field, with a source position
but no `theorem` keyword; the audit enumerated 272 theorems, the guard counted 267, and `make lean` failed (the
cross-check worked). Projections are kernel projections and carry no axioms. Rule: the audit excludes
`isProjectionFn` constants and says so in its header. Check: the count comparison in `audit.rs` stays strict.

## 14. `leanchecker` on the root module was OOM-killed (2026-11-06)
With 21 modules, `leanchecker OscInt` (which re-checks every submodule in one process) reached 13.5 GB resident and
was killed by the memory cgroup; the replay reported a FAIL with an empty message while every per-module run and all
six export kernels passed. Rule: replay per submodule only; the root module may only import. Check: `replay.rs` skips
the root; `guard.rs` rejects anything but imports in `OscInt.lean` (test `root_module_imports_only`).

## 15. "Lead-verified" was weaker than it read (2026-11-06)
The adversarial review showed that module build + guard + `#print axioms` + type check accept a `False` theorem
added by a `run_tac` metaprogram with kernel checking switched off (option name built from strings). Only kernel
replays catch it; the final claim rested on them. Rule: verifying an agent's part includes per-module
`leanchecker`, and the guard forbids metaprogramming entry points in library files. Check: guard tokens and tests
(`run_tac`, `open Lean`, `Lean.`, `set_option`, …); `replay.rs` per-module `leanchecker` including Blueprint.

## 16. Commits during a referee run blur "this commit" (2026-11-06)
Post-proof referee A started on c355ee7 and finished on d932c0d because the lead committed in between; untracked
review files would also have marked the final replay record DIRTY. Rule: freeze the tree while referees or the final
`verify-all` run (park new files in the scratchpad), and give referees the commit to review. Check: the replay record
prints DIRTY for any untracked or modified file.

## 17. Sanity witnesses must separate what a plant could swap (2026-11-06)
Calibration round 2 caught all four plants, but three reports showed that the real sanity theorems would not have:
`sanity_Fold_hyps` uses `K = K'` (blind to a `K`/`K'` swap), `sanity_D4_hyps` uses x³ + y³ with zero mixed
coefficients (blind to a wrong `ddd` index in `cubicCoeffs`), and the S2.2 sanity theorem restates its hypothesis.
Why it matters: the referee is the only line of defence against such errors when the sanity checks are degenerate.
Rule: sanity witnesses use generic data — distinct sets for distinct roles, all coefficients nonzero and distinct,
and at least one "bite" instance where the hypothesis fails and the definitions must say so. Check: none automatic;
the S4 file `OscInt/D4/Sanity.lean` follows it (coefficients (1, 2, 3, 5); elliptic case shown excluded).

## 18. A check that never looked at proofs passed everything (2026-11-06)
The first `GammaFree.lean` collected constants through `ConstantInfo.value?`, which at this Lean version returns
`none` for theorems (they count as opaque unless `allowOpaque := true`). It followed definitions and types only,
so every "Gamma-free OK" on a proof was vacuous; its negative control (`Real.Gamma_pos_of_pos`) mentioned Gamma in
its *type*, so the control could not catch this. Found when the proof's closure (4 493 constants) was barely larger
than the statement's (4 492), and referee B's independent count was 33 082. Rule: every check gets a negative
control that exercises the exact path the check exists for (here: a theorem whose type is clean and whose proof
uses Gamma), and suspicious counts are investigated before a PASS is reported. Check: `gammaProofControl` in
`GammaFree.lean` (must be rejected); after the fix the statement closure is 33 099 and `OscInt.d4ConstantPos`
43 612 constants, still clean.

## 19. The hand-off's S4.4 route needed a lemma that exists only for real rates (2026-11-06)
The hand-off planned I = Γ(2/3)/2 "by an Abel limit of `integral_cpow_mul_exp_neg_mul_Ioi`" with rate ε − i. The
name exists (as `Complex.integral_cpow_mul_exp_neg_mul_Ioi`), but its rate is `r : ℝ` with `0 < r`, so the route
would have needed analytic continuation; found by `#check` before any agent started, replaced by a real-variable
route through the Beta integral (`docs/proof-S44.md`). Why it mattered: lesson 1 checks that names exist; a name
with the wrong hypotheses fails just as late. Rule: a route's lemmas are `#check`ed with their full signatures, and
the route says which hypothesis of each it uses. Check: `MathlibNames.lean` (`#check @name` prints the signature;
the S4.4 names are added there).

## 20. A blueprint elaborated against too few imports hid a name clash (2026-11-06)
The S4.4 blueprint and assembly compiled in a scratch file importing only `OscInt.Statements.D4Limit`; the route
referee found that `OscInt.Blueprint.NormalFormFacts` already existed (`Blueprint/StationaryPhase.lean`), so the
committed blueprint would have broken the default build and every part that imports `OscInt.d4ConstantPos`. Rule:
elaborate a new blueprint and its assembly against `import OscInt` and `import Blueprint` (the environment the parts
will see) before review. Check: once committed, `make quick` builds both libraries; before that, the lead's scratch
file starts with those two imports.

## 21. A fresh machine without `zstd` and `bwrap` failed `verify-all` after 50 minutes (2026-11-06)
`verify-toolchain` (archive extraction needs `zstd`) and the `lake check --paranoid` step of `lean-replay` (sandbox
needs `bwrap`) failed on a new container; every other step passed, and after `apt-get install zstd bubblewrap` the
two failed checks passed on the same export. CI installs both, so only local runs were exposed. Rule: verify-all
checks its system tools before running anything and names the package to install. Check: `verify_all` preflight
(unit test `missing_tools_are_named`).

## 22. A downstream checker hashed the sources and trusted the build (2026-11-07)
The first `tools/oscint_check.py` checked that the statement files had their stamped hashes and that the proving
theorem had the statement's type and clean axioms. The adversarial referee passed it with a package whose statement
constant was redefined as `True` in another module, and with a theorem added under `debug.skipKernelTC`; neither
check looked at what the build actually contains. Why it mattered: the README told downstream projects this proved
they depend on exactly the reviewed statements. Rule: a check verifies the artefact that is used (the loaded
environment: the constant's module, its commitment, the kernel's verdict on the `.olean`), not a proxy for it (a
source hash), and its documentation says what it does not cover. Check: `tools/test_oscint_check.sh` (a control
for each path, including both of the referee's reproductions).

## 23. A front-end bridge drafted before its statement's review cost the "fixed before proof" claim (2026-11-07)
For F1 and F2 the lead wrote and compiled the bridge proofs (about 30 lines) in the scratch directory while the tree
was frozen for another run, then stamped and reviewed the statements. Nothing changed afterwards and both reviews
were FAITHFUL, but the order can no longer be claimed, and the docs and `OscInt/API.lean` had to say so. Why it
mattered: a short, obvious proof is exactly where the temptation is greatest and the cost of waiting smallest. Rule:
no proof code for a statement, even in scratch, before its stamp and blind review; check the assembly against the
parts only when the parts are blueprint hypotheses. Check: none automatic (scratch is outside the tree); the hand-off
lists it under process notes.

## 24. A referee proved the statement it was reviewing (2026-11-07)
In the blind pre-proof review of batch 2, referee A checked that C5 is true by proving it in its own scratch
(`simp only [disc, Cubic.discr]`) and disclosed it. Harmless here (one line, after the stamp, outside the tree), but
"no proof existed before the review" is then true only of the lead and the repository, and a referee that proves a
statement has stopped reviewing its meaning. Rule: pre-proof referee prompts say "do not prove the statements under
review; numerical and counterexample checks only", and the docs state the claim at the strength the evidence has.
Check: none automatic (referee scratch is outside the tree); the prompt template.

## 25. `make stamp` refuses a dirty tree, after the commitment step (2026-11-07)
An untracked referee prompt made `make stamp` fail at its last step, after nine minutes of commitments and exports,
so the whole target ran twice. Rule: park every new file in the scratchpad before `make stamp` (as for referee runs,
lessons 16), and commit the prompt after the stamp. Check: `stamp create` already refuses (correct); a preflight
`git status --porcelain` in the `stamp` target would fail in seconds instead of minutes (added 2026-11-10:
`make stamp-preflight`, the first prerequisite of `stamp`, with its negative control recorded in the commit message).

## 26. Mathlib renamed `Cubic.disc` to `Cubic.discr` (2026-11-07)
The plan for C5 named `Cubic.disc` from memory; `#check` at the pin found only `Cubic.discr` (and
`discr_eq_prod_three_roots`, `discr_ne_zero_iff_roots_nodup`). Caught before the statement was written (lessons 1
working as intended). Rule unchanged: `#check` before writing a statement; the new names are now used by a frozen
statement, so `MathlibNames.lean` should list them (added 2026-11-10).

## 27. The guard matches theorem names by their last component (2026-11-07)
A challenge theorem `OscInt.API.dd_eq_iteratedFDeriv` was flagged because an internal lemma
`…ImplicitAux.dd_eq_iteratedFDeriv` exists; the guard demanded a `#assert_type_is` line for a theorem not yet
declared. Conservative (a false positive, not a hole); renamed the API theorem instead of changing the guard, since a
guard change needs an adversarial review. Rule: public API names must not repeat an internal short name. Check: the
guard itself.

## 28. A referee's Lean process OOM-killed the replay (2026-11-07)
`make verify-all` on 9e5540a reported `FAIL leanchecker OscInt.API` with an empty message: the memory cgroup killed
`leanchecker` at 13.5 GB while three referees ran Lean on the same machine (one `import OscInt` was enough). The
step was correct to fail and the record cannot be used. Why it mattered: the final replay is the evidence, and a
contended machine turns it into noise (lessons 14 had the same signature). Rule: the final `verify-all` runs with no
other Lean process on the machine; referees run before or after it, never during. Check: none automatic; the replay
record names the commit and the run's isolation in its header.

## 29. A fast proof campaign outran the order claim (2026-11-07)
The statement-first order held for the Lean proofs of batch 2 (stamp, two blind reviews, then proof agents), but the
adversarial referee showed that the docs claimed more than the evidence: the reviews were not timestamped, the route
with its algebraic certificates was drafted during the review window, and the derivative-level sanity file was
written while the agents ran although the answers said "before". Why it mattered: "frozen and reviewed before the
proof" is the claim that makes "as stated" credible, and it must rest on timestamps, not on commit order. Rule:
stamp the review reports (a stamp of the tree after the review commit) before launching proof agents, and word the
claim as "statements timestamped; no Lean proof before the reviews (git order, reviews stamped at …)". Check: none
automatic; the hand-off checklist.

## 30. `leanchecker M` replays every module whose name starts with `M` (2026-11-07)
After front-end batch 2 added eight `OscInt.API.*` modules, `leanchecker OscInt.API` went from 11.5 s to an OOM kill
at 13.46 GB (limit 14.3 GB), alone on the machine. The toolchain source (`src/lean/LeanChecker.lean`) selects
`target.isPrefixOf m` and replays the matches in parallel tasks, each with its own imported environment; lessons 14
saw the same for the root. Why it mattered: the replay could not pass, and the first diagnosis (a referee's
concurrent process, lessons 28) was wrong until the step was re-run alone. Rule: no module except the root has
submodules; library code that belongs to a namespace with an entry-point module lives in another directory
(`OscInt/Front/`). Check: `tools/check_entry_point.sh` (in `make quick`), with a self-test of the detector. After moving a module,
delete its old build outputs (`.lake/build/lib/lean/<old path>`, `.lake/build/ir/<old path>`), or the replay's
stale-build check fails, as it did once on c462966 (lessons 5 working).

## 31. The hand-off described a state the owner had already changed (2026-11-08)
The session-5 brief said `main` = cb39601 with the session-4 branch unmerged and the release perhaps unpublished; in
fact PR #4 was merged (6acef2a) and v0.3.0 published hours earlier. Acting on the brief would have opened a duplicate
pull request and prepared owner steps that were already done. Rule: the first action of a session is to read the
remote state (`git fetch`, the releases API, the latest CI run on `main`) and record any difference from the brief in
the session checklist (`handover_corrections`) before planning. Check: none automatic; the checklist field.

## 32. A shallow clone made `stamp-verify` fail on the oldest stamp (2026-11-08)
The session container's clone was shallow; `make stamp-verify` stopped at `stamps/20261105T203058Z-7516eb518dce`
("ci.yml not found at 7516eb5…") because the stamped commit was not present. After `git fetch --unshallow` every
stamp verified. The check was right to fail (lessons 9 is the CI form of this). Rule: unshallow before
`stamp-verify` or `verify-all`; a stamp failure that names a missing commit is first checked with
`git rev-parse --is-shallow-repository`. Check: none automatic (an actionable message in `stamp` would be a tool
change; it needs an adversarial review, candidate for ROADMAP §4 "actionable error messages").

## 33. Sanity theorems through the statement constant, with planted controls (2026-11-08)
Both API3 pre-proof referees found that the sanity theorems restated the hypotheses (lessons 11 again), so a plant in
a statement body (`p ↦ −p`, `p ↦ 0`, `+L ↦ −L`, "everywhere") would leave them green. Answered before any proof by
theorems that take the statement constant as a hypothesis and apply it to data on which the plant makes the
discharge impossible, and by compiling planted copies (four rejected, unplanted copies accepted). Why it matters:
this tests the frozen text itself, which a restated hypothesis cannot, and it needs no re-freeze. Rule: from the next
batch on, write sanity theorems in this conditional form (or bundle each hypothesis as a `def` shared with the
statement, lessons 11), choose data that separate each new feature (generic, p ≠ 0, k ≠ 0, a sign that matters,
lessons 17), and run at least one planted copy per statement before the stamp. Check: `OscInt/Front/FamilySanity.lean`
compiles in `make quick`; the planted controls are a record (`docs/replay/2026-11-08-API3-sanity-plants.txt`), not yet
a CI job.

## 34. A quadrature rule chosen from habit would have made a pre-registered check meaningless (2026-11-08)
The first draft of the P3b protocol used composite Simpson with 4096 panels up to m = 640; its error term is O(1) there
(about 1.25 rad of phase per panel), so the check would have measured the quadrature, not the remainder. Caught while
writing the program, before the run; replaced by the trapezoid rule, which converges faster than any power for
integrands vanishing to all orders at the boundary once π/h exceeds the largest frequency. Rule: a pre-registered
numeric protocol states the resolution argument (frequency versus step) and an a-posteriori quadrature check
(|I_n − I_2n| against the quantity measured), and is revised only before its first run. Check: the protocol template
in `docs/prereg/`.

## 35. Two intermediate pushes were red; both checks were right (2026-11-08)
CI `quick` failed on e42dcd3 (the pins added ten statements to `stamps/statements.json` that `import OscInt.API` did
not yet expose; entry-point check) and on 3b05946 (proof files declared theorems named in `comparator-API3.json`
without `#assert_type_is` lines; guard). Locally only targeted commands had run before those pushes (`make
statements`, `make commit`, `lake build <module>`), not `make quick`. Both were fixed by later commits on the branch;
`main` was never red. Rule: run `make quick` before every push, including "intermediate" ones, and read the CI result
of the previous push before the next claim (lessons 9). Check: none automatic (a pre-push hook would be one).

## 36. A record cited in an answer file did not exist (2026-11-08)
The API3 answers cited "the second part of `docs/replay/2026-11-08-API3-sanity-plants.txt`" for the M2 plants; the file
had one part (one commit), and the outcome lived only in a commit message. Found by the step-5 rule referee in session
6, not by the post-proof or adversarial referees who read the same answers. Why it mattered: a waiver drafted on the
answers would have claimed controls that were never recorded. Rule: cite a record only by a path (and, for a part, a
heading) that exists in the tree at the commit that cites it; re-run and record rather than cite a commit message.
Check: none automatic yet (a link checker over `review/` and `docs/` for backticked repository paths is cheap).

## 37. One push without `make quick`, docs-only (2026-11-08)
Session 6 pushed 3581074 (memo, records, a numerics binary) before running `make quick`, on the judgment that nothing
Lean-facing changed; the run afterwards passed. The judgment was right this time and is exactly what lessons 35 says
not to rely on. Rule unchanged (lessons 35): `make quick` before every push. Check: none automatic (a pre-push hook).

## 38. Sanity data must contain every point type a statement distinguishes (2026-11-08)
The first GD sanity file tested GD and GD-C only on the elliptic umbilic x³ − 3xy², which has no fold points, so a
plant replacing "fold or nondegenerate" by "nondegenerate" passed; and every D4 datum sat at 0 inside K, so plants
evaluating the D4 conditions at 0, or requiring D ⊆ K, passed (pre-proof referees A m1, m3; B m1, m2). Answered
before any proof by x³ + y³ (folds on the axes), a translate with its D4 point at (1, 1), a D4 point outside K, and a
critical-points-only datum; 15/15 plants rejected. Rule (extends lessons 17): for each case split a statement makes
(point types, exceptional sets, inside/outside K, critical vs pointwise) at least one datum lies in each branch.
Check: the plant generator `docs/replay/plants/2026-11-08-GD/plants_gd.py.txt` (one plant per branch).

## 39. A comment changed a hash: `sorry` records its source position (2026-11-08)
Adding licence headers (comments only) to the `Challenge/` files changed all eleven challenge exports, so every
comparator configuration would have been rejected against its stamp. The challenges are statements with `sorry`
proofs, and at this Lean version each `sorry` carries its source position; shifting the file by seven lines changes
the exported term. Found by re-exporting and comparing with the stamped hashes before committing, not by assuming
"comments are inert". Rule: a file whose build product is hashed by the trust chain (statement files, challenge files)
is never edited for any reason, comments included; its metadata goes in `REUSE.toml`. Check: `make comparator`
(export hash against the stamp), and the session re-export comparison recorded with the licensing change.

## 40. Ten red CI runs went unread (2026-11-08)
Every push of session 6 failed CI at the toolchain install (an unpinned elan download during a GitHub outage); the lead
noticed only when the owner asked for a CI review. The failures were infrastructure, but a real failure would have gone
unseen just the same. Rule (lessons 9 again): read the CI result of each push before the next claim. Check: the
`verify / verdict` and `ci` checks as required status checks under branch protection (owner item).

41. **Run every new CI command line locally once, verbatim, before pushing the workflow.** The redesigned `verify`
    comparator matrix called `challenge check ROOT CONFIG STAMP`, a subcommand the tool's doc comment described but its
    argument dispatch never had; all 11 comparator jobs exited 2 on the usage message (PR #6, run 42485206068).
    actionlint cannot see this. Fixed by adding the dispatch arm; checked by running the job's exact command on
    `comparator-GD.json` (accepted, exit 0) and against a wrong stamp (exit 1).
42. **Do not write proofs in the working tree while a route referee runs; park them outside the repository.** In batch
    LE (session 7) the lead wrote the parts' proofs while the route referee was reading, and the referee saw the
    untracked files (`review/2026-11-08-LE-route-referee.md`, M1). The mathematics was not at risk, but the claim "route
    reviewed before any part was proved" was lost. Write drafts under the scratchpad until the route review is committed.
43. **A grid classifier cannot see sub-grid degeneracies; check symmetry lines and refine near small fold quantities.** The
    batch-VV classification reported QWZ m = 3 as "nondegenerate or fold everywhere" (grid 2π/2048) although the k₁ ↔ k₂
    symmetry forces exact cusp points on the diagonal wherever H₁₁ = H₁₂ (`docs/design/vector-amplitudes.md` §6). The cusp
    control was a large one; add a positive control whose cusp lies between grid points, and solve the symmetry-reduced
    equations exactly before trusting a "folds only" verdict.
44. **A planted control counts as rejected only if the planted claim is shown false.** In batch A3 the plant "constant
    10k − 12" (28 at k = 4) failed to compile against `vdCk_chain4` only because the copied proof closed with `exact this`
    against the bound 38; with `exact this.trans (by norm_num)` it compiled, so the plant was not detected (a smaller
    constant strengthens the conclusion). Rule: for every rejected plant, give semantic evidence (a compiled witness that
    the planted predicate holds or fails on the datum, a robust closing that still fails, or an exact computation), and
    record script-only rejections as not detected. Check: the A3 plant record lists the evidence per line.
45. **A recording script must not write its own output file in the tree while it records the tree's state.** The census
    spec-check record first said "tracked files modified: yes" on a clean tree: the shell had truncated the tracked output
    file before the script ran `git status`. Rule: write the record outside the tree, then copy it in, and check the
    record's commit and dirty lines before committing it. Check: the commit messages of the A3 and CENSUS records.
46. **No chats, prompts or verbatim AI-conversation text in the repository or its history (owner rule, 2026-11-10).**
    Session 9 recorded external review chats and a reviewer's packet verbatim, and a referee prompt, following the old
    CONTRIBUTING step 5. The owner had already declined to record a sweep brief. Custom prompts and conversation text
    are sensitive fingerprints that can identify people, so they count as personal data. Rule: record external reviews
    and referee reports only as the lead's answers, in the lead's own words. Paraphrase rather than quote; a short
    quotation of a paper title, of Mathlib, or of the repository's own text is fine. Never commit a prompt, the owner's
    or a referee's. Name an external tool only in an AI-use disclosure (tool and version, as COPE and ICMJE ask), never as an author
    or credit, and only where its output enters the work (as for the S5.1′ route, 2026-11-10). The lead's commit attribution trailer is unchanged; it was already on 158 commits of
    `main`. The branch history of session 9 was rebuilt without those
    files. Earlier prompts and verbatim reports on `main` are an open owner item: removing them from `main`'s history
    would invalidate every stamp. Check: none automatic yet; a candidate `make quick` check for `review/prompts/`
    additions and for transcript markers is in ROADMAP "Standing: repository hygiene".
