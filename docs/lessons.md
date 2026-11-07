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
