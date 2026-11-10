# Answers to the CENSUS spec-fidelity referee (2026-11-10)

Subject: the draft specification `docs/prereg/2026-11-09-CENSUS-spec.md` and pre-registration
`docs/prereg/2026-11-09-CENSUS-prereg.md`, with `numerics/census/spec_checks.py`, at db4cc7d, before any implementation
exists and before registration. One fresh-context referee, read-only. Its prompt and report are not recorded (lessons
46); its findings are stated here in the lead's words. Its own scripts (SymPy eliminations and grid scans) were not
committed; what they showed is summarised below and disclosed in the registration's §1.

## Verdict

One BLOCKER, nine MAJOR, ten MINOR, three NIT, one informational note. All accepted; every repair is in the spec's
§8 entry of 2026-11-10 and in the registration text. Because a blocker was found, a second fresh referee checks the
repairs before the spec is frozen.

What the referee confirmed with its own code (not with `spec_checks.py`):
- the M08 reference values of spec §7 (`H[w,w]`, `T[v,v,w]`, `Q[v⁴]`, `g4 = −5247/√65`), from an expansion in the
  `(s, u)` coordinates;
- the K-QWZm closed forms at the four masses, and the decimals of `g4`, `v_m`, `a_m`, `2π/3 − a_{201/100}` and `H[w,w]`;
- the Σ sets of K1, K2 and K3, the K2 formulas `det H = 24Y³ − 4X²` and `−480τ⁸`;
- K5: no point of Σ off the two lines (exact elimination in a half-angle chart, then the symmetry `k ↦ k + (π, π)`);
- §2 is a partition of every point; its A2 and A3 conditions agree with the Lean predicates `FoldCondSpan`,
  `IsA3Point` and `IsStableA3Point`, and D4 with `IsD4Point` (the spec's discriminant is 6⁴ times Lean's `disc`, same
  sign and zero set);
- the corpus formulas and NS sets, re-derived by hand;
- `spec_checks.py`: 36/36 PASS at that commit.

Its grid scans, which are hints and not proofs: four candidate cells for M17 near `(±π/2, ±π/2)`; four for M18 near
`(±2π/3, 0)` and `(0, ±2π/3)`; M03's points `±(π/2, π/2)` are A3; no stable cusps for M07.

## Findings

| Finding | Severity | Answer |
|---|---|---|
| B's NS-ADJACENT label applied to any box that merely touches the 2⁻¹⁰ ball around an NS point, however large, and no order of the label tests was fixed. A large box so labelled would let the two-implementation statement cover ground B never examined. Also, B could evaluate closed forms on a box that contains an NS point and label it EXCLUDED. | BLOCKER | Accepted. Spec §6 now fixes the order: NS (enclosure of `u` disjoint from `J`), then NS-ADJACENT (enclosure of `u` not inside `J`, and box width ≤ 2⁻¹²; wider boxes are split), then EXCLUDED and A3-PROVEN, both only where the enclosure of `u` lies in `J`. The two-implementation statement (registration §4) is now made outside the union of B's NS, NS-ADJACENT and UNRESOLVED boxes, not outside a fixed ball, so no distance on T² is needed. |
| `g4` depends on the length of the kernel vector, and the spec let either kernel vector be used. The relative tolerance of C4(a) and the absolute threshold of C5(a) therefore fail for a correct implementation (at M08 the kernel-formula vector gives a value about 10⁹ times smaller than §7's). | MAJOR | Accepted. Spec §2.3 defines `ĝ4 = g4/\|v\|⁴`; every value and threshold uses it. §7 gives `ĝ4` for M08 (`−5247/(4√65)`), K-QWZm and K1 (`ĝ4 = −6`, confirmed by check K1; `g4` is −24576/625 with `v_a` and −7776/625 with `v_b`). Spec §2.4 adds the scale-free `D̂ = Disc/max(\|a\|,\|b\|,\|c\|,\|d\|)⁴`; C5(a) uses `ĝ4` and `D̂`. |
| The registered run never ran K-QWZm and gave it no IDs, so C4(a) could not be evaluated, making the study NOT DISCRIMINATING by construction. | MAJOR | Accepted. Steps 3–4 now run every record of `numerics/census/corpus.json`, which includes `K-QWZm[201/100]`, `[5/2]`, `[4]` and `[10]`; the IDs are also in spec §5. |
| K3's E/J point lies on its A3 segment, so by §2.5 it is E/J + NI, which the expectation omitted; the schema could not say where on a component a type occurs; K5's two lines are one component. | MAJOR | Accepted. §2.5 defines special points of one-dimensional components; the schema has `special_points` and typed `samples`; K3 and K5 are stated as one component each with their special points. |
| "B's boxes cover the domain exactly (dyadic)" is impossible on `(−π, π]²`, whose side is irrational. | MAJOR | Accepted. B's root box is the dyadic square `[−4, 4]²` on T² (overlap is harmless by periodicity); C3(b) tests every lift of a point. |
| Any Σ curve exhausts B's 2²⁴-box budget long before width 2⁻⁴⁰, and the spec did not say how unfinished boxes are labelled. | MAJOR | Accepted. Boxes are processed breadth-first; on exhaustion every queued box is UNRESOLVED, so the labelled boxes always cover the root box, and C2 and C3(a) stay defined. |
| The PASS wording "contains an A-object" would let an UNRESOLVED box hide further Σ points, and "contains" is undefined for components given by samples. | MAJOR | Accepted; merged with the blocker's repair (statement outside the union U). |
| C5(b) needs B's per-box enclosures, which the schema did not contain; the start and mapping of the random points were not fixed. | MAJOR | Accepted. B provides an enclosure interface (`numerics/census/impl_b/enclose.py`), cheaper than storing enclosures for up to 2²⁴ boxes per model. C5(b) fixes `x₀ = 20261109`, point j from `x_{2j+1}` and `x_{2j+2}`, and the mapping onto T² and onto the box. |
| No machine-readable input: implementers would transcribe the table by hand, "cannot be parsed" was undefined for H, and NS was assumed finite. | MAJOR | Accepted. `numerics/census/corpus.json` is the authoritative input; check CORPUS proves each record identical to the spec's formula. Each implementation computes NS itself; the schema has `ns_components`. Pool entries use the same grammar and are validated before sealing. |
| The held-out draw left choices to the selector at the reveal: which drand chain, how the hash input is encoded, what "canonical JSON" means; the registration time relied on git's committer date; the inclusion rule would be sealed with the pool and so could be written afterwards; "lowest-ranked" was ambiguous after replacements. | MAJOR | Accepted. Spec §3 fixes the default mainnet chain by its hash, the key `SHA-256(R ‖ 0x00 ‖ UTF-8(id))` over the raw randomness bytes, JCS (RFC 8785) for the pool, a 16-byte random salt, an RFC 3161 and OpenTimestamps stamp of the registration commit before the round's time, the inclusion rule in clear text now, and original ranks for the replacement step. |
| The E/J label included the zero cubic, which is Arnold's X9 class and deeper, not E or J. | MINOR | Accepted. New type X (`C = 0`); family F-X added to the ranking list. K5's crossings and M07's point `(π, π)` are X. |
| "NI" read as "non-isolated critical point", which K3's A3 points are not. | MINOR | Accepted; NI is defined explicitly in §2.5 as "on a positive-dimensional component of Σ". |
| `spec_sha256` "at the frozen commit" conflicts with changes allowed after freezing. | MINOR | Accepted: the registered commit, in the schema and in C1. |
| Step 7 did not say that it runs from a clean checkout with H outside the tree. | MINOR | Accepted; also the SHA-256 of the pool and H files are recorded with the verdict. |
| The size of H ("4–6") did not match the draw of 5 minus dropped models; C7 was undefined for a recommended pair; models failing C4(b) or C5 were still counted in N(F). | MINOR | Accepted. H has 5 models; C7 needs at least 3; pairs are compared with pairs; N(F) counts only models that pass C3, C5 and, where it applies, C4(b). |
| C5(a) said "scaled by" without saying divided or multiplied, and named no norm. | MINOR | Accepted; explicit inequalities with the max-entry norm. |
| Implementation A: `exact` was optional although C3(b) needs it; overlapping charts produce duplicates; the denominators of the `ρₘ` were not mentioned. | MINOR | Accepted; all three now stated in §6. |
| The verification key cited the prior-art sweep, which commit 88872ae removed from the tree. | MINOR | Accepted; the spec and the registration now point to it in history (`git show 58a86d0:…`). |
| `cubic_root_structure` in `spec_checks.py` called a cubic with roots at 0, ∞ and a third point (for example `κ₁κ₂(κ₁ + κ₂)`) "double". | MINOR | Accepted and fixed (a root at infinity has multiplicity 3 − deg); new check R4 tests it. No earlier check had such a cubic, so no earlier result changes. |
| The sign convention of the kernel was never written as a formula. | MINOR | Accepted; spec §0 gives `K = ∫ e^{i(tΨ + x·k)}`, as Lean's `latticeKernel` (checked in `OscInt/Statements/Global.lean`). |
| No schema field for FLAT. | NIT | Accepted: `flat`. |
| "Every phase is machine-checked" was not true for M03, M04, M16 or M10's NS set. | NIT | Accepted; §3 now says which are checked and which are derived by hand. |
| GD-F and GD-N have hypotheses beyond the GD-covered predicate. | NIT | Accepted; §4.2 says the predicate is necessary, not sufficient, for them. |
| Informational: M07 (QWZ, m = 1) has `u ≡ 1` on `k₁ = π` and `k₂ = π`, so these lines are Σ curves of type A≥4 + NI, with `H = T = 0` at `(π, π)`; the registration's expectation that M07 has A3 points has no support. | (note) | Confirmed exactly: `u = 1 + 2(1 + c₁)(1 + c₂)`, check M07-LINES. The expectation in registration §1 is replaced, before registration, and the facts are in spec §7. |

## What the referee did not check

The literature statements (it had no web access), the drand verification mechanics, whether the GD theorems are
proved in Lean, the complete Σ set of any corpus model beyond its grid scans, and the full held-out protocol against
the computation-of-record procedure.

## Second part: the referee of the repairs (2026-11-10)

Subject: the same files at 2e288c1, after the repairs above. A second fresh-context referee, read-only, with its own
code. Its prompt and report are not recorded (lessons 46).

**Verdict:** no BLOCKER; four MAJOR, seven MINOR, six NIT, all accepted and repaired before freezing (spec §8, third
2026-11-10 entry).

What it confirmed with its own code:
- the blocker's repair: no test order, root box, processing rule or budget rule lets the two-implementation statement
  cover a point that no B test examined, including points of T² with several lifts;
- `ĝ4` is the same for both kernel vectors and four choices of `w` (25 digits) at every K-QWZm and M08 point, and every
  §7 value;
- `corpus.json`, with its own parser and transcription;
- exact eliminations: Σ of M07 is exactly the lines `k₁ = π` and `k₂ = π`, and Σ of K5 is exactly `c₁ + c₂ = 0`;
- the held-out replacement step ends after at most one iteration (200 000 simulated pools).

| Finding | Severity | Answer |
|---|---|---|
| The special points introduced by the first repair, and A's NS points, were tied to no cross-check: a spurious special point inside an EXCLUDED box of B would fail no criterion. | MAJOR | Accepted. C3(b), C3(c) and C5(a) now cover special points and sample points; A's NS points and NS-component samples may not lie in a box whose enclosure of `u` lies in `J`. NS components now carry samples in the schema. |
| §2.5 listed "ends" among special points, so K3's segment ends on the box boundary would be special points and contradict the K3 expectation, failing C2. | MAJOR | Accepted. Ends on ∂B are not special points; a Σ curve has no end at NS. A component may have no special points. |
| B's schema required fields that interval branch and bound cannot decide (`flat`, NS points, fold set empty). | MAJOR | Accepted. Those fields are `null` for B. |
| Coverage of a component containing an X point was ambiguous between F-NI and F-X, which could flip the recommendation via M07. | MAJOR | Accepted. Every point on a positive-dimensional component, special points included, is covered by F-NI alone; the other point families count isolated points only. |
| `ĝ4` scales like Ψ, so an absolute threshold is not scale-free. | MINOR | Accepted; the C5(a) bound for A3 is relative (`σ = ‖Q‖ + T[v,v,w]²/\|H[w,w]\|`), and the spec states the scaling. |
| C5(a) checked only A3 and D4 and not the rank. | MINOR | Accepted; one condition set per type, including the binary cubic's Hessian covariant for E/J (verified by the lead: it vanishes exactly for a cube). |
| C3(c) and the §4 wording had no lift rule. | MINOR | Accepted; both speak of lifts; U's area is reported within `[−π, π]²`. |
| The acceptance control rejected a component without special points, which can be legitimate. | MINOR | Accepted; the field must be present and may be empty. |
| The inclusion rule was not mechanical (which parameter values, a failing fallback, domain assignment, when to stop, coordinates, band, an unnamed validator). | MINOR | Accepted; all fixed in spec §3 (60 examined sources, a domain order, `numerics/census/validate_pool.py`). |
| The selector could void H after seeing it by mishandling the reveal. | MINOR | Accepted; the owner reveals from custody, and a voided H is a reported outcome. |
| CORPUS checked only `G` and `u`, and the M07 component claim went beyond its check. | MINOR | Accepted. CORPUS checks every field, unique ids and family totals (a planted wrong weight makes it fail); the M07 wording says the lines lie in one component, and the referee's elimination is disclosed. |
| B's `ĝ4` enclosure undefined off Σ; child order and "processed" ambiguous; output size; JCS rounds numbers; K-SQ omitted X and C4(a) used control names as IDs; the 48-hour rule not verifiable. | NIT | Accepted; fixed `v` and `w`, explicit child order and budget count, gzip allowed, pool values as strings with unique ids, K-SQ lists X, C4(a) names M08 and M17, and the 48 hours run from the RFC 3161 stamp time. |

What it did not check: the literature statements, the drand chain hash against the network, complete Σ sets beyond M07
and K5, whether Krawczyk tests succeed at the corpus's A3 points, A's charts, the Lean predicates, and whether the GD
theorems hold.
