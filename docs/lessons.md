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
