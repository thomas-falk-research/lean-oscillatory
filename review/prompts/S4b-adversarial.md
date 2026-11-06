# Adversarial review: S4.1′, S4.2, S4.3

You are a hostile, competent referee. Find what is wrong with the claims "S4.1′, S4.2 and S4.3 are machine-checked as
stated" and "the S4.3 proof is Gamma/Beta/Mellin-free" in `/home/user/lean-oscillatory`
(`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time, `nice -n 10`; scratch files only under `/tmp/adv5/`;
do not edit repository files, git state, or `build/`; do not run `make` targets).

Attack at least:
1. The statements (`OscInt/Statements/D4Limit.lean` against `docs/statements.md` S4): junk values (`limUnder`,
   non-integrable `angularMoment`), whether `D4LimitStatement` has bite (e.g. specialise to x³ + y³ and a fixed
   amplitude with A(0) ≠ 0 and derive that t^{2/3}·|∫| converges to a positive number), whether S4.1′ really
   contains the elliptic case, and the Gamma-free claim (write a theorem whose type is Gamma-free and whose proof
   uses `Real.Gamma` and confirm `GammaFree.lean`'s machinery rejects it; look for ways a forbidden constant could
   hide: auxiliary `_proof_` constants, `opaque`, instances, `Decidable` terms).
2. The proof route: `docs/proof-S42.md`, `docs/proof-S43.md`, `Blueprint/D4Limit.lean`, `Blueprint/D4LimitS42.lean`,
   `OscInt/D4/*.lean`. Could a part have been proved through a loophole? Does the S4.2 assembly use the S4.3 and
   S4.1′ results exactly as frozen?
3. The trust chain: comparator configs and pins for the new stamp, `StatementTypes.lean`, `Axioms.lean`, the replay
   record, CI.
4. The prose: `README.md`, `docs/STATUS.md`, `docs/HANDOFF.md`, `docs/decisions/2026-11-06-S4.md`, `docs/lessons.md`
   (entry 18): overclaims or understatements.
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix.
First line: `git rev-parse HEAD`.
