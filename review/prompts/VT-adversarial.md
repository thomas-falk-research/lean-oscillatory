# Adversarial review: batch VT and the QWZ finding

You are a hostile, competent referee. Find what is wrong with these claims, in `/home/user/lean-oscillatory` at the
commit the lead names (`. ~/.leanenv`; one Lean process at a time, `nice -n 10`; scratch only under `/tmp/advVT/`; do not
edit repository files, git state or `build/`; do not run `make` targets):
(a) "GD-C-V, GD-V, GD-F-V, GD-N-V are machine-checked as stated (verify-all PASS on d261c19), frozen (stamp
    20261108T235416Z-961cebc296ef) and blind-reviewed (reviews stamped 20261109T002419Z-45505299011a) before any proof,
    and the route review was committed before the part's proof entered the repository";
(b) "the sanity theorems detect the plants the record says (second run: 7 rejected), including 'C after E' against
    the uniform-family theorem for a semantic reason";
(c) "the QWZ m = 3 model failed its pre-registered decay check (t^{-2/3} observed, not t^{-5/6}), and the diagnosis is
    near-separability: D4 points split into folds with tiny margins" (`docs/design/vector-amplitudes.md` §4–5,
    `numerics/results-qwz-decay-2026-11-08.txt`, `docs/prereg/2026-11-08-VV-qwz-decay.md`): is the reading right? is
    the diagnosis right? was anything frozen or claimed that the failure should have stopped?
(d) the records (README, STATUS, CHANGELOG, HANDOFF, ROADMAP): overclaims or understatements about VT and VV.
Attack at least: the transfer proof's integrability and continuity argument, universe handling, instance diamonds
(`NormedSpace.complexToReal` against other ℝ-structures), junk values, whether "one constant for every E" is really
what is proved, and the plant generator. Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line,
failure scenario, and fix. First line: `git rev-parse HEAD`. Return the report as your final message.
