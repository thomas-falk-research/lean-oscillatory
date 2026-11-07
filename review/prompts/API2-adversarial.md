# Adversarial review: front-end batch 2, the release preparation, and the release-pin check

You are a hostile, competent referee. Find what is wrong with the claims (a) "the fourteen batch-2 statements are
machine-checked as stated and were frozen and reviewed before any proof", (b) "v0.3.0 is prepared: tag commit
2e8707a, SHA-256 pins in `docs/release-notes/v0.3.0.md`", and (c) "CI fails when the README's pinned tag does not
exist" in `/home/user/lean-oscillatory` (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time,
`nice -n 10`; scratch only under `/tmp/advAPI2/`; do not edit repository files, git state or `build/`; do not run
`make` targets).

Attack at least:
1. Statements and proofs: `OscInt/Statements/Convert.lean` against `docs/statements.md`; the assembly
   `OscInt/API/Convert.lean` and the parts; junk values (`fderiv` of a non-differentiable function is 0,
   `Matrix.rank`, `𝓝[≠]`, operator norms on `ℝ × ℝ`), hypotheses that are never satisfiable, front ends that are
   weaker than their docs say. Use `examples/consumer/ConsumerFormula.lean` and `OscInt/API/ConvertSanity.lean`.
2. The order claim: git history (`git log --format='%h %ci %s' -- OscInt/API OscInt/Statements/Convert.lean
   review/2026-11-07-API2*`), the stamp `stamps/20261107T101640Z-4acb308f54f4` (verify its manifest commit), the
   referees' disclosure. Is anything in the docs stronger than the evidence?
3. `tools/check_release_pin.sh` and CI job `release-pin` (`.github/workflows/ci.yml`): can a missing tag, a wrong
   tag, a tag on a commit whose `stamps/statements.json` differs from the notes, or a README pin in another syntax
   (e.g. `rev = 'v0.3.0'`, a `lakefile.lean` `@ "v…"`, a pin only in a code comment) pass? Does the self-test cover
   the paths it claims? Is `consumer-release` sound (what does it check, what does it trust)?
4. Release notes and CHANGELOG: are the SHA-256 values those of the files at 2e8707a (`git show
   2e8707a:stamps/statements.json | sha256sum`)? Are the "Statement changes" claims true against `git show
   v0.2.0:stamps/pins.txt`?
5. The prose: `README.md`, `docs/STATUS.md`, `docs/HANDOFF.md`, `CHANGELOG.md`: overclaims or understatements.
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix.
First line: `git rev-parse HEAD`. Return the report as your final message.
