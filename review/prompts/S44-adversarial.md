# Adversarial review: S4.4, and the new dependency surface

You are a hostile, competent referee. Find what is wrong with the claims "S4.4 is machine-checked as stated" and
"a downstream project can check that it depends on exactly the reviewed statements" in `/home/user/lean-oscillatory`
(`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time, `nice -n 10`; scratch files only under
`/tmp/adv6/`; do not edit repository files, git state or `build/`; do not run `make` targets).

Attack at least:
1. The statement and proof: `OscInt/Statements/D4Limit.lean` (S4.4) against `docs/statements.md`; the route
   `docs/proof-S44.md` (which changed the hand-off's route), `Blueprint/D4ClosedForm.lean`, `OscInt/D4/ClosedForm.lean`
   and the part files (`CubicComp`, `GammaSixth`, `CosMomentValue`, `Chart`, `Covariance`, `NormalForm`, `Beta`,
   `LineMoments`, `ClosedFormFinal`). Could a part have been proved through a loophole (junk values, a hypothesis
   that is never satisfiable, `cubicComp` not being the coefficients of C ∘ g)? Specialise the closed form to a
   cubic with all coefficients nonzero and compare with an independent numerical evaluation of c_C.
2. The trust chain for S4.4: `comparator-S44.json` and its pin, `StatementTypes.lean`, `Axioms.lean`, the replay
   record named in `docs/STATUS.md`, CI.
3. The dependency surface: `stamps/statements.json` and its generator `tools/src/bin/statements.rs`,
   `tools/oscint_check.py`, `tools/test_oscint_check.sh`, `examples/consumer/`, README "Depending on OscInt",
   `docs/policy.md`. Can a modified OscInt pass `oscint_check.py` (a changed definition in the closure with an
   unchanged statement file; a proving theorem whose type is the statement only up to defeq; a statements.json
   that omits a statement; an axiom the check does not see)? Is the re-freeze rule in `docs/policy.md` sound and
   does it claim more than it delivers?
4. The prose: `README.md`, `docs/STATUS.md`, `docs/HANDOFF.md`, `CHANGELOG.md`, `docs/lessons.md` (entries 19–21):
   overclaims or understatements.
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix.
First line: `git rev-parse HEAD`. Return the report as your final message.
