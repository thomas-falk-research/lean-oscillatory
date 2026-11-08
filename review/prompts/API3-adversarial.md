# Adversarial review: front-end batch 3 (API3) and the session-5 release-pin change

You are a hostile, competent referee. Find what is wrong with the claims (a) "the ten API3 statements are
machine-checked as stated, and were frozen and blind-reviewed (reviews stamped) before any Lean proof", (b) "the
pre-proof MAJOR (sanity theorems restate hypotheses, lessons 11) is answered without re-freezing, by
`OscInt/Front/FamilySanity.lean`", and (c) "CI job release-pin now fails when main pins a release commit that HEAD does
not contain", in `/home/user/lean-oscillatory` (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time,
`nice -n 10`; scratch only under `/tmp/advAPI3/`; do not edit repository files, git state or `build/`; do not run
`make` targets).

Attack at least:
1. Statements and proofs: `OscInt/Statements/Family.lean` against `docs/statements.md`; `OscInt/Front/{Family,
   FamilyC10,Cutoff,Local}.lean`. Junk values (`fderiv` of a non-differentiable function is 0; `iteratedFDeriv` of a
   function smooth only on `U`; Bochner integral of a non-integrable function is 0), hypotheses that are never
   satisfiable, conclusions weaker than the docs say, quantifier order, the max norm.
2. The order claim: `git log --format='%h %ci %s' -- OscInt/Statements/Family.lean OscInt/Front review/2026-11-08-API3*
   docs/proof-API3.md stamps/`; verify that each stamp's manifest names the commit it claims
   (`stamps/20261108T002603Z-9d03130c8f3a`, `stamps/20261108T010546Z-7bb457958327`) and that no proof file of the batch
   is in either manifest. Is anything in the docs stronger than the evidence?
3. The decision in `review/2026-11-08-API3-pre-proof-answers.md` not to re-freeze after a MAJOR (CONTRIBUTING step 5
   says "A BLOCKER or MAJOR means a new statement, never an edit"): is the reading defensible, or is it a weakened rule
   to get green? Do the theorems of `FamilySanity.lean` and the negative controls
   (`docs/replay/2026-11-08-API3-sanity-plants.txt`) actually detect the plants they claim? Reproduce at least one
   control in scratch, and look for a plausible plant they miss.
4. `tools/check_release_pin.sh` check 4 and `.github/workflows/ci.yml` job `release-pin`: can a release commit not
   contained in main pass (shallow clones, a tag that is an ancestor through a different path, a missing
   `.commit` file, `git merge-base` errors swallowed by `2>/dev/null`)? Does the self-test cover the path?
5. The prose: `README.md`, `docs/STATUS.md`, `docs/HANDOFF.md`, `CHANGELOG.md`, `docs/session-5-checklist.json`:
   overclaims or understatements.
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix.
First line: `git rev-parse HEAD`. Return the report as your final message.
