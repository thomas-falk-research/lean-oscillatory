# Adversarial review: batch GD, the API index tooling, and the session-6 records

You are a hostile, competent referee. Find what is wrong with these claims, in `/home/user/lean-oscillatory` at the
commit the lead names (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time, `nice -n 10`; scratch only
under `/tmp/advGD/`; do not edit repository files, git state or `build/`; do not run `make` targets):
(a) "the eight GD statements are machine-checked as stated, and were frozen (stamp 20261108T094842Z-edf7787a2845) and
    blind-reviewed (reviews stamped at 20261108T102629Z-8c8d7b090adb) before any Lean proof";
(b) "the sanity theorems through the constants detect the plants the record says (15/15), at the mutated hypothesis";
(c) "`tools/gen_api.py` with `tools/test_gen_api.sh` makes `docs/api.json` and `examples/api/Snippets.lean` fail CI on
    drift; the index is generated from the source where possible";
(d) "T6 with `examples/consumer/ConsumerLattice.lean` gives the ℓ¹ → ℓ^∞ dispersive estimate t^{-2/3} for the 2D lattice
    Schrödinger propagator, and T6L with SH shows it is sharp";
(e) the owner memo `docs/decisions/2026-11-08-step5-memo.md` and the v0.4.0 notes `docs/release-notes/v0.4.0.md` are
    accurate and leave the decisions to the owner.
Attack at least: junk values (Bochner integral of a non-integrable function is 0; `fderiv` of a non-differentiable
function is 0; `iteratedFDeriv` of a function smooth only on U; `m ^ σ` for m ≤ 0), quantifier order, the max norm,
the order claim (`git log --format='%h %ci %s'` over the batch files and `stamps/`; each stamp manifest's commit and
contents), the plant generator (does a rejection fall at the mutated hypothesis, or could brittleness explain it?
reproduce at least two plants and find one plausible plant that is missed), the API generator and its self-test
(can drift pass? does `lean_statement` come from the stamped file? are hand-written annotations checked against
anything?), the consumer example's definition of the propagator (is it the propagator of the stated equation?), and
the prose in README, STATUS, CHANGELOG, ROADMAP, HANDOFF, `docs/session-6-checklist.json`, `docs/which-theorem.md`,
`docs/applications.md` (overclaims or understatements; every "demonstrated" must point at a compiled file).
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix. First line:
`git rev-parse HEAD`. Return the report as your final message.
