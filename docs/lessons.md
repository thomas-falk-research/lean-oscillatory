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
