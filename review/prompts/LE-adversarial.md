# Adversarial review: batch LE, the session-7 tool changes, and the session-7 records

You are a hostile, competent referee. Find what is wrong with these claims, in `/home/user/lean-oscillatory` at the
commit the lead names (`. ~/.leanenv`; one Lean process at a time, `nice -n 10`; scratch only under `/tmp/advLE/`; do not
edit repository files, git state or `build/`; do not run `make` targets):
(a) "T0E, T6F, T6E are machine-checked as stated (verify-all PASS on a1d2a64), and were frozen (stamp
    20261108T160847Z-4a183530559f) and blind-reviewed (reviews stamped at 20261108T164514Z-c91a9a8bb0b6) before any
    Lean proof of them"; the lead admits the route referee ran while the parts were being written;
(b) "the sanity theorems detect the plants the record says (9 rejected, 1 recorded blind spot)";
(c) "the pre-registered numeric checks (`docs/prereg/2026-11-08-LE-lattice-constants.md`, amendment 1; and
    `docs/prereg/2026-11-08-VV-classify.md`) were registered before their programs existed and their results are
    reported as run" (check `git log --format='%h %cI %s'` on the prereg, program and result files);
(d) "the 2D kernel of T6/T6L factorises, so T6/T6L are classical" (`docs/prior_art.md`): is the disclosure accurate
    and complete, and is anything still overclaimed in README, STATUS, CHANGELOG, applications, ROADMAP, release notes?
(e) the tool changes `tools/src/bin/stamp.rs` (`stamp verify-every`: every stamp directory, no files written into
    stamps/) and the hash-locked CI installs (`tools/requirements-ci*.txt`, `.github/workflows/ci.yml`): can a bad or
    unpinned stamp directory pass? can an unhashed package be installed?
(f) `docs/design/vector-amplitudes.md`: is the duality route correct as written (integrability, the junk value of a
    non-integrable Bochner integral, real vs complex scalars for `iteratedFDeriv`, `exists_dual_vector''`)? Is the
    QWZ classification result read correctly (`numerics/results-classify-vv-2026-11-08.txt`)?
Attack at least: junk values (`Real.rpow` at 0 and negative bases; Bochner integral of a non-integrable function), the
constant algebra, the five-piece split, Fubini's hypotheses, quantifier order, and overclaims ("explicit constant" is
true, but is it useful? is that said?). Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line,
failure scenario, and fix. First line: `git rev-parse HEAD`. Return the report as your final message.
