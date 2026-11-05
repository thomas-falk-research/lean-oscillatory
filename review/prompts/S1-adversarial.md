# Adversarial review: milestone M1 (S1, van der Corput)

You are a hostile, competent referee. Your job is to find what is wrong with the claim "S1 is machine-checked as
stated" in this repository, not to confirm it.

Repository: `/home/user/lean-oscillatory` (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time,
`nice -n 10`; scratch files only under `/tmp/adv/`; do not edit repository files or git state).

Attack, at least:
1. The statements (`OscInt/Statements/VanDerCorput.lean` against `docs/statements.md`): vacuity, hypotheses weaker
   or stronger than claimed, Lean conventions that collapse a case, ill-conditioned regimes (ν, μ → 0; a = b;
   derivatives unbounded at endpoints; amplitudes with integrable but unbounded derivative; very large p). Try to
   PROVE in Lean a consequence that would be absurd if the statement were vacuous, or find a hypothesis set that is
   satisfiable only trivially.
2. The trust chain: could the final theorems prove something other than the stamped statements? Check
   `StatementTypes.lean`, `comparator.json` (are the theorem names right; is `definition_names` empty), the
   commitment tools (`tools/lean/CommitEnv.lean`, `tools/src/canon.rs`, `docs/commitment-format.md`: what does the
   commitment NOT cover, and does that matter here), the axiom audit (`Axioms.lean`, `tools/src/bin/audit.rs`: can a
   theorem escape enumeration), the guard (`tools/src/bin/guard.rs`), the replay (`tools/src/bin/replay.rs`).
3. The numbers: run `make numerics` only if you have 5 minutes of CPU; otherwise read
   `numerics/results-2026-11-05.txt` and the source and say whether the probes test the Lean hypotheses as stated.
4. The prose: `README.md`, `docs/STATUS.md`, `docs/prior_art.md`: anything overclaimed or understated?

Report every finding as BLOCKER / MAJOR / MINOR / NIT with the exact file and line, the failure scenario, and a fix.
First line: `git rev-parse HEAD`.
