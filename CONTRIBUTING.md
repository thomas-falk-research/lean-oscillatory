# Contributing

OscInt's value is its trust chain: a reader checks the kernel, three axioms, and a short frozen statement, and
nothing else. Every contribution keeps that chain intact. Read `docs/lessons.md` first; each lesson is a rule.

## The local loop
```bash
lake exe cache get          # once: Mathlib binaries
make quick                  # build, guard, axiom audit, statement types, Gamma-free check (minutes)
make verify-all             # the full replay (about an hour); CI runs it on main and weekly
make verify-all ONLY=guard  # one step of verify-all, with the same pass/skip rules
```
Use `nice -n 10 lake env lean -DautoImplicit=false <file>` to iterate on one file (`lake env lean` does not apply
the lakefile's `leanOptions`). Never run `leanchecker` on the root module `OscInt` (lessons 14).

## Hard rules (checked by `make guard` and the audit)
- No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `@[extern]`, `opaque`, `macro`,
  `elab`, `syntax`, `notation`, `run_cmd`, `run_tac`, `#eval`, `open Lean`, `Lean.`-qualified names, `attribute`,
  or `set_option` other than `set_option maxHeartbeats N in` in library files. Write `∞` for C^∞ (`ContDiff ℝ ⊤` is
  analytic here, lessons 12).
- Theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- A stamped statement file (`OscInt/Statements/`) is never edited. A change is a new statement.
- No weakened statement or test to get green. A part that is false is reported with a counterexample.

## Adding a statement, end to end
The order matters: the statement is frozen and reviewed before any proof exists, so "as stated" can be claimed.
1. **Mathematics.** Write the statement in `docs/statements.md`: hypotheses, conclusion, modelling choices, and
   what it omits relative to the source.
2. **Lean statement.** A `def XStatement : Prop` with a docstring starting `**<label>**` (the label and summary go
   into `stamps/statements.json`), a pin `theorem statement_pin_X : XStatement = XStatement := rfl`, sanity
   theorems on generic data (distinct coefficients, distinct sets for distinct roles, lessons 17) and a bite
   instance where a hypothesis fails and the definitions must say so. Each hypothesis is either a
   named `def` shared by the statement and its sanity theorems, with a bite instance proving its negation on data
   (lessons 11, 17), or tested by a sanity theorem that takes the statement constant as its only hypothesis and
   discharges it on generic data (lessons 33); in the second form at least one planted copy per statement is run and
   recorded, with the compiler output, under `docs/replay/plants/` before the stamp (owner decision 2026-11-09). `tools/target/release/scaffold <Name> <label>` (once it exists,
   ROADMAP §4) generates the skeleton; until then copy `OscInt/Statements/D4Limit.lean`.
3. **Challenge and comparator.** `Challenge/<File>.lean`: the final theorem with a `sorry` proof (never imported).
   A `comparator-<id>.json` naming that theorem. `make challenge-export`.
4. **Freeze.** Commit; `make commit` (both commitment producers must agree); `make stamp` (RFC 3161 ×3,
   OpenTimestamps ×2); add the pin lines to `stamps/pins.txt` (statement and `challenge:` lines); `make
   statements` regenerates `stamps/statements.json`; commit and push.
5. **Blind review.** Two fresh-context referees review the statement against `docs/statements.md` without seeing any
   proof. Prompts are not committed, and reports are not reproduced verbatim (owner privacy rule 2026-11-10, lessons
   46). The answers file under `review/` records each finding in the lead's words, with its severity and the evidence
   it cites. A
   BLOCKER or MAJOR means a new statement (back to 2), never an edit. A MAJOR whose finding is only against the prose
   of `docs/statements.md` (not the Lean text, not the sanity layer) is answered by a dated clarification there,
   recorded in the answers file with the referee's finding stated in the lead's words (owner decision 2026-11-09,
   `docs/decisions/2026-11-08-step5-memo.md`).
6. **Route and blueprint.** `docs/proof-<id>.md` (the mathematical route, each step with the Mathlib names it needs,
   each name `#check`ed at the pin, lessons 1); `Blueprint/<File>.lean` (one `def …Facts : Prop` per part); the lead's
   assembly `theorem x_of (h₁ : …Facts) … : XStatement` compiled before any part is proved. Check every interface
   numerically. A route referee reads route and blueprint; findings are folded into a "Revision after the route
   referee" section.
7. **Proofs.** One file per part under `OscInt/<Area>/`, by proof agents or people, under the briefs in
   `review/prompts/`. Integrate each part: `lake build <Module>`, guard, `#print axioms`, per-module `leanchecker`,
   commit.
8. **Final theorem.** `theorem OscInt.x : Statements.XStatement := x_of part₁ …` in a short final file; add it to
   `StatementTypes.lean` (`#assert_type_is`) and import it from `OscInt.lean`.
9. **Replay.** On a frozen, committed tree (lessons 16): `make verify-all`; record the output in `docs/replay/`.
10. **Post-proof review.** Two blind post-proof referees and an adversarial referee; answers in `review/`.
11. **Records.** The STATUS row (derived from the evidence, never typed as a claim), a progress-log entry, CHANGELOG,
    README status table, `docs/HANDOFF.md`. A user-facing theorem also gets an example and a docstring that cites
    the textbook statement it formalises.

## Changing a proof (no statement change)
Refactors are welcome: the statement types are fixed, so `make quick` (types and audit) and the replay are the
regression test. Keep each declaration under about 60 lines; helpers go in an `…Aux` namespace. Do not use `private theorem`: the
axiom audit (`Axioms.lean`) skips internal names such as private ones, so its count no longer matches the guard's
and `make quick` fails (found 2026-11-07; the strict count is the safety net, lessons 13).

## Commits and releases
Commit messages say what changed and what evidence was run. Releases follow `docs/policy.md`. Prepare a release
in a pull request: bump `lakefile.toml`, `CITATION.cff` and `.zenodo.json` together, add the CHANGELOG section
`## vX.Y.Z`, and write `docs/release-notes/vX.Y.Z.md` with the SHA-256 rows of `stamps/statements.json` and
`tools/oscint_check.py` (`tools/release_preflight.sh X.Y.Z` checks all of this locally and prints the exact rows).
After it merges, the owner dispatches `release-candidate` on `main` with the version (Actions → release-candidate →
Run workflow): it re-runs preflight and the full replay on that commit, builds the assets with `SHA256SUMS` and a
Sigstore build-provenance attestation, and prints the exact commands; the owner creates the tag and the GitHub
release with them (CI never writes tags or releases). Publishing triggers `post-release`: the tag must be on `main`
and have a successful candidate run, the published assets must be the attested ones, `examples/consumer-release` is
built against the tag, and a pull request records `docs/release-notes/vX.Y.Z.commit` and moves the pins. Zenodo
then mints the version DOI.

CI (`docs/decisions/2026-11-08-ci-release-review.md`): `ci.yml` (quick, tools, consumer) on every pull request and on
`main`; `verify.yml` (the replay, in parallel jobs, verdict in `verify / verdict`) on pull requests to `main` that
are not drafts, on `main`, weekly and from the release; open pull requests as drafts while work is in progress.
