# Answers to the external R3 research packet (six-target triage; T5 and T8 selected), 2026-11-13

Subject: three archives and a decision brief from the same external reviewer as
`review/2026-11-13-application-chains-answers.md`. They were written against 24a68cc, whose tree is identical to the tree
of this branch's HEAD at review time (2cf118d, the merge of the same work). The archives, the prompt and the chat are
not recorded (owner privacy rule, lessons 46). Each claim is restated in the lead's words, with the evidence the lead
produced. Written by the session-11 lead.

## Summary

- **Integrity: PASS.** Every archive digest matches the relayed list, and every manifest entry matches. Archive 2 binds
  Archive 3 correctly.
- **The mathematics: TRUE as hand mathematics** (T8 P1–P4, T5 P5.1–P5.4, and the T2, T6, T7 and T10 claims checked).
  - None of it is machine-checked.
  - Everything checked is classical.
  - No referee found a BLOCKER in the mathematics.
- **The draft Lean does not elaborate as shipped.** Three mechanical repairs make it elaborate; details below.
- **Novelty: none, and the packet claims none.** Its central T8 item, the signed alias identity on the −π grid with the
  observation that accuracy tests cannot see the sign, was already found here on 2026-11-10
  (`review/2026-11-10-external-dossier-answers.md`, item C6, check F3b). The packet does not cite that record.
- **T5, the evidence profile: no new guarantee for OscInt.** The packet itself scores this U = 0. R1–R9 restate checks
  that this repository already enforces, in full or in part. The design has three MAJOR defects, listed below.
- **One error in this repository:** `docs/calibration.md` rounded four Clopper–Pearson bounds in the unsafe direction.
  Corrected in this commit.
- **Recommendation: nothing to freeze now.**
  - T8 is a better-specified input to the existing ROADMAP item I7, whose gates are unchanged: I7 comes after I1, I2 and
    A3, and it needs a matrix-valued model and a second unrelated reuse.
  - T5 is kept as a record.

## What arrived

- **Archive 1, triage** (SHA-256 4b9d82ac71be24def24252b7be8b531354b76d7273747f7994e6579d21bc48b2).
  - Reports on six targets: T2 caustics, T5 an evidence profile, T6 exponential sums, T7 windows and chirps, T8 a
    Fourier error package, T10 physical scope.
  - A fixed-rule ranking, source and query ledgers, and four exact-arithmetic scripts with their expected outputs.
- **Archive 2, statements** (3da3f401758839ef16fc89fc969a6136c8c8ff35c166eba9b4ee8a2ee0426709).
  - Four T8 statements, with planted variants and a hypothesis-control table.
  - A draft Lean file with four `…Statement : Prop` definitions and four conditional sanity theorems, and a list of
    `#check` candidates.
  - The T5 requirements R1–R9, two JSON schemas, draft claim cards, a draft certificate and a pilot design.
  - The SHA-256 of Archive 3.
- **Archive 3, proofs** (a71bfcff9987f1e1eb80dce1713b90af46e2d05630e62ec1a1cc6d79475b3a01).
  - Hand proofs P1–P4 for T8 and P5.1–P5.4 for T5.
  - Two audits by the reviewer's own assistants.
- **A decision brief** (PDF).
- **The packet's own framing.**
  - It calls itself INCOMPLETE and not freeze-ready.
  - No Lean was run: the reviewer's environment had no `lean` executable.
  - It makes no priority claim, and every score is labelled a judgment.
  - It asks that Archive 3 be opened only after the statements are frozen and blind-reviewed.
- **AI-use disclosure.** The packet was produced with ChatGPT (exposed model name GPT-6 Astra Pro), as it states, using
  four instances of that model. Its two audits are by the same model family. The lead has not verified the model version.

## What the lead did

1. **Integrity.**
   - Computed the three archive digests and compared them with the relayed list: all match.
   - Checked all 107 manifest entries with the lead's own code: no mismatch, no missing file, no unlisted file.
   - Checked that Archive 2's recorded digest of Archive 3 is the delivered Archive 3.
   - Checked the digests that the packet's audits cite against the delivered files. All match except the T5 draft claim
     card, which the packaging notes say was given evidence digests after review (NIT).
2. **The packet's scripts.**
   - Read them first: standard library only, with no subprocess, network, `eval` or `exec`.
   - Ran each on a copy in a sandbox with no network (`bwrap --unshare-all`) under Python 3.13.18; the packet used
     3.12.14.
   - All four outputs are byte-identical to the packet's expected files.
   - These scripts mostly re-assert closed forms. For example, the T8 script never sums the grid. So the run confirms
     their arithmetic, not their claims.
3. **Lean.** The lead installed the pinned toolchain from `toolchain.sha256` (archive hash OK) and the Mathlib cache,
   built `OscInt.Statements.VanDerCorput`, and elaborated the drafts from a scratch copy outside the tree. Results:
   - **As shipped, both files fail** at the first command. Each places `import` after a module docstring, which Lean 4
     rejects.
   - **With the imports moved first (diagnostic copy):**
     - All 15 `#check` candidates exist at the pin.
     - The statements file still fails in two places:
       - It sums with the removed `∑ k in s` syntax.
       - One sanity theorem coerces a real power into ℂ, so Lean looks for a complex-to-real power instance (`HPow ℂ ℝ`)
         that does not exist.
   - **With those two also repaired:**
     - The four statement definitions elaborate.
     - The four sanity theorems compile.
     - `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.
   - These repairs are the lead's. They show that the content elaborates, not that the packet's file does.
   - The sanity theorems take every analytic hypothesis as an argument, so they do not show that the hypotheses can be
     met on data (lessons 33).
   - No proof of any statement was written (lessons 23).
4. **The lead's own checks.** `numerics/review/r3_packet_checks.py`, record
   `numerics/results-r3-packet-checks-2026-11-13.txt`: 26/26 PASS. Every check is computed from first principles
   (direct grid sums, quadrature, Bessel functions, Beta quantiles), not from the packet's closed forms.
   - The first run had five failures, all in the lead's own harness:
     - tolerances of 1e-40 on oscillatory quadrature over infinite ranges;
     - an equality case off by 2e-61;
     - a function missing from mpmath 1.3.0.
   - They were fixed before the recorded run.
5. **Reading.**
   - Read in full:
     - the brief;
     - the top-level notes of all three archives;
     - the T8/T10 report;
     - every Archive 2 statement file;
     - the T8 and T5 proofs, the T8 audit and the computation notes.
   - Read by referees in full, and by the lead only in the parts that bear on a verdict: the T2, T6/T7 and T5 triage
     reports and the ledgers.
   - **Order:** the lead opened Archive 3 at 22:00:26Z, after the Lean elaboration and the lead's own statement-level
     checks.
6. **Four fresh-context referees** (Claude instances, same model family as the lead), launched at 2cf118d. Times are
   each referee's own `date -u`:

   | Referee | Scope | Start | Finish |
   |---|---|---|---|
   | Blind statements | Archive 2 and the repository only. Barred from Archive 3 and Archive 1. No proving (lessons 24). It reports opening neither. | 21:56:07Z | about 22:14Z (last `date -u` 22:14:01Z) |
   | Proofs | Archive 3 step by step. | 21:56:07Z | 22:06:17Z |
   | Triage mathematics | T2, T6, T7, T10, the ranking, and the packet's statements about the repository. | 21:56:06Z | 22:08:51Z |
   | T5 and citations | T5 against this repository; web check of the key citations. | 21:56:07Z | 22:09:47Z |

   - None ran Lean, lake or make.
   - None could write a report file (harness rule), so their reports exist only in the session record.

## Verdicts by target

**T8, a Fourier error package. TRUE (hand proofs re-checked; not machine-checked; classical).** The four statements:
- **T8-1:** absolute tails of the inverse transform and of the omitted samples. For a power envelope A(1 + |u|)^{−p} the
  bound is A(1 + T)^{1−p}/(π(p − 1)).
- **T8-2:** Poisson periodisation of a continuous f with period L = 2π/h. The error of the truncated inverse sum is at
  most an explicit alias term plus the T8-1 tail.
- **T8-3:** on the grid k_j = −π + 2πj/N, the sampled coefficient equals Σ_ℓ (−1)^{N Σℓ_a} c_{n+Nℓ}, with geometric
  bounds in one dimension and in two dimensions (an ℓ¹ coefficient envelope on a max-norm window).
- **T8-4:** for an amplitude written as φ′q, with q absolutely continuous, q′ integrable and q → 0, the improper
  oscillatory tail is at most (|q(T)| + ∫|q′|)/|t|.

What the lead checked:
- Every step of P1–P4. The proof referee did the same independently.
- The identity, numerically, for generic complex coefficients in one and two dimensions (error about 1e-31). The
  unsigned form misses by at least 0.0087 at odd N.
- The proof referee also checked matrix-valued coefficients.
- The acceptance example (the Poisson kernel at r = 1/2) by direct grid summation:
  - the least N meeting 10⁻⁶ is 21, with error 2/2097153;
  - the unsigned envelope also passes at 21;
  - the monomial controls give −1 at N = 3 and +1 at N = 2.
- Both geometric budgets hold. T8.3c is attained at n = 0 (lead) and, by the same construction, at every |n| < N (proof
  referee; the packet claims sharpness only at n = 0). T8.3d is attained at R = 0, n = 0.

Findings (the lead's checks and the proof referee's; no BLOCKER, no MAJOR):
- **MINOR.** The statement file says the Poisson-kernel example has a slightly better odd-grid threshold than the uniform
  condition. At the stated tolerance this is false: the uniform condition, the unsigned envelope and the exact signed
  error all give N = 21. Only the error value at 21 is smaller. Checked by the lead (MINOR-1 in the record).
- **NIT.** The alias bound holds as written for R < 1 + L, not only R < L.
- **NIT.** One comparison series is called a "power series"; it is a p-series.
- **NIT.** The consumer is named without the suffix the README uses.

The blind statement referee, which saw no proofs, found all four prose statements TRUE and all twelve planted variants
false (semantic evidence for each). No BLOCKER. Its findings, which concern the draft Lean layer, not the mathematics:
- **MAJOR: the sanity theorems cannot detect plants in the statement bodies.**
  - Each sanity theorem only instantiates its statement. Every analytic hypothesis is an argument, and no budget or
    left-hand side is ever evaluated.
  - The data are degenerate: A = 1, x = R = 0, n = 0, T = 0, φ′ = 1.
  - The referee gave eleven plants, each shown false on data, that the theorems would accept. Examples:
    - a halved tail constant;
    - a budget at T < 0, which Lean's real power makes 0 or negative;
    - an alias budget without its integral term;
    - every change to the alias sign;
    - q(T) replaced by q(0);
    - φ′q replaced by q;
    - dropping t ≠ 0.
  - This breaks lessons 11, 17, 33, 38 and 47.
- **MAJOR: the Lean layer has no parity control.**
  - I7 asks for a negative control in which the unsigned identity, or the wrong parity, fails.
  - The T8-3 sanity theorem uses only the bound part. That part stays exactly true under a zero-origin plant, so the
    draft cannot tell signed from unsigned.
  - The monomial controls exist only in prose.
- **MAJOR, predicted before the lead's run: `∑ k in` fails to parse.** Confirmed by the lead's elaboration (above).
- **MINOR, predicted before the lead's run: the real power coerced into ℂ.** Also confirmed.
- **MINOR: the T8-1 and T8-3 claim cards describe more than their Lean declarations cover.**
  - The T8-1 declaration has only the power-envelope bound: no general tail inequality, no sampled tail.
  - The T8-3 declaration is one-dimensional and scalar, with the bound at n = 0 only.
  - The T8-4 declaration needs C¹ data on all of ℝ.
  - Only the T8-3 and T8-4 narrowings are disclosed in the packet.
- **MINOR: the endpoint plant needs another witness.** The triangular witness for T8-4 is not C¹, so it cannot reject a
  planted copy of the C¹ Lean draft. A C¹ smoothstep does: 1.978 > 1.
- **NIT.**
  - The table row on max-norm envelopes understates its case. Reusing the ℓ¹ formula under a max-norm envelope is false,
    not merely unjustified: at n = 0 the max-norm sum is 8x/(1 − x)², twice the formula's 4x/(1 − x)², with x = r^N.
    Checked by the lead by shell counting.
  - CLAIMS.json cites an Archive 3 path for a file that is in Archive 2.

**Mathlib already has T8-2's identity.** `Real.tsum_eq_tsum_fourier_of_rpow_decay` is Poisson summation for a continuous
f with f and its Fourier transform both O(|x|^{−b}), b > 1, up to rescaling and the sign convention. The lead checked it
with `#check` at the pin. A formal T8-2 would be a corollary of it, not new formalisation.

**What is new to the project.**
- Already here (2026-11-10 dossier answers, C6, F3b; ROADMAP I7):
  - the signed identity;
  - the observation that an accuracy-only test cannot tell signed from unsigned.
- New in R3:
  - a scalar statement set with conventions written out;
  - exact monomial parity controls, which are cleaner than the earlier N = 5 floating-point discrimination;
  - an exact acceptance example;
  - a Lean draft that is close to elaborating.

None of this meets I7's deliverable, which is a matrix-valued QWZ model with an independently checked enclosure, or I7's
stop rule, which needs a second unrelated reuse. The packet says the same.

**T5, an evidence profile. Mathematics TRUE; no new guarantee; three MAJOR design findings.**
- **What holds.**
  - The Clopper–Pearson endpoints and the 86-versus-85 threshold are correct. The lead checked them with Beta quantiles
    and exact integers; the T5 referee reproduced them independently.
  - The multiplicity counterexample is correct: two 95% intervals at n = 86 and p = 1/2 have joint coverage 0.92188.
  - The status-reducer argument is correct. The proof referee enumerated 130,820 configurations with no violation.
  - Every statement the packet makes about OscInt's trust chain is accurate. The T5 referee checked each one against the
    repository with file and line.
- **What OscInt already has.** R1, R2 and R5 are enforced here. R4, R6 and R9 are mostly covered. R3, R7 and R8 are
  partly covered. Where OscInt falls short of the profile:
  - referee isolation is by instruction only, with no access record;
  - checker start and end times and resource limits are not recorded per checker;
  - there is no mechanical per-claim reducer with rules for duplicate, conflicting and unknown observations;
  - STATUS rows are not invalidated automatically when a dependency changes.
- **MAJOR, the schema.** The certificate schema cannot hold what R3 and R6 require. Its `checks`, `reviews` and
  `chronology` objects forbid extra fields and have no fields for checker times, separate exit and semantic outcomes,
  resource limits, reviewer access sets or isolation records. Checked by the lead in the schema.
- **MAJOR, chronology.** Chronology is two booleans set by the producer. There is no field for the timestamp token, its
  authority or its root. The packet's own rule is that a producer cannot confer acceptance by writing a field, so this
  contradicts it. OscInt already re-verifies RFC 3161 tokens from three authorities against pinned roots.
- **MAJOR, the pilot passes only with zero errors.** With 86 items at 97.5%, one miss gives a lower bound of 0.928 < 0.95.
  - The pilot therefore passes only on 172/172.
  - With true detection rate 0.99 and bad-event rate 0.01 the chance of passing is 0.178; at exactly the targets (0.95
    and 0.05) it is 0.00015.
  - Checked by the lead (MINOR-2 in the record; raised to MAJOR here, as the T5 referee rated it).
  - The packet says this is not a power calculation, but never says that a single miss fails.
- **MINOR.**
  - The two-sided Bonferroni construction needs 86 items. A one-sided bound per target controls false acceptance with
    59 (72 with Bonferroni).
  - Pre-exposure failures and defective items are not defined.
  - The reducer fixtures and the R8/R9 prose disagree on whether a mismatched digest gives FAIL or INCOMPLETE.
  - The gap analysis omits `tools/oscint_check.py` and the Sigstore release attestation.
  - Monotonicity in P5.1 is argued informally.

**T2, caustics (triage only). TRUE as stated, conditional on the local inputs.** The packet's account of the repository
is accurate: the A3 and D4 definitions, GD, and the open I3 item.
- The pointwise-classification assembly is correct.
- The linear-phase cancellation counterexample is correct.
- The A3 line of x⁴ + y² is correct.
- The flat example (y + x²/2)² is correct.
- The separated-phase constants and the thresholds 2547, 16483 and 61047 are correct; each is the least integer.

Findings:
- **MINOR.** The one-dimensional ingredient of the separated-phase bound is OscInt's own machine-checked S1.k (the same
  constant 5·2^{k−1} − 2, uniform in the linear term). The packet re-derives it by hand without citing S1.k.
- **NIT.** The packet proves the constant 6 for k = 2 but uses 8. Its thresholds are therefore those OscInt can certify
  today, not the best the hand argument gives (1334, 8196 and 28723). It should say so.

**T6, exponential sums (triage only). TRUE where checked.**
- The Kusmin–Landau bound cot(πδ/2) ≤ 2/(πδ) is correct, and 2/π is asymptotically optimal.
- The Weyl differencing factor is correct.
- OscInt's S2.2 is a magnitude bound with no B-process expansion.

Findings:
- **MINOR.** "Corrected" 2/π rests on a source the packet did not read.
- **MINOR.** Not checked here: the transcriptions of the Yang and Patel–Yang remainders, and the content of the Salt
  formal development. The T5 referee confirmed that the Salt files exist at the cited commit.

**T7, windows (triage only). TRUE.**
- C^m alone, even for a nonnegative compactly supported taper, gives no |u|^{−m−1} envelope. The lacunary counterexample
  is correct.
- The bounded-variation replacement is correct.
- For the normalised ideal Hann aperture, the supremum over |u − s| ≥ 7/2 is 8/(315π), which is −41.847 dB.

Finding:
- **MINOR.** The cut at 7/2 lies inside the second sidelobe, which peaks at u = 3.4079 with −41.479 dB (checked by the
  lead). So −41.847 dB is the envelope value at the cut, not a sidelobe level. The region |u| ≥ 3 still meets −40 dB, with
  supremum −41.479 dB.

**T10, physical scope (triage only). TRUE.**
- The kernel normalisation is correct.
- C₀ = C*/(2π) = 4(1 + √7)/(3π), and the usefulness threshold J|t| > C₀³/2 ≈ 1.8522 is correct.
- Landau's constant sup x^{1/3} J₀(x) = 0.7857468705 is correct.
- The contour example is correct: e⁶/65536 at z = 8, n = 16. The lead also computed |J₁₆(8)| = 7.8e-5.
- The finite-volume recurrence is correct.
- The Duhamel bound is correct.
- The defect eigenvector is correct.
- The quartic point at J₂ = −J/4 is correct.
- The free-fermion anticommutator is correct.
- The endpoint control 1/(1 − it) is correct.

**Ranking.** The scores 6, 4, 1, 0, 0, 0 and the third-target rule are applied as stated. The scores are the reviewer's
judgments.

**Citations.** The T5 referee checked the priority sources and a sample of the T2 and T6/T7 entries, with URLs in the
session record. All exist and say what the packet claims; none is fabricated. The Necula and Lee papers and Landau's journal paper
were checked by metadata only (Landau's conference version was read).

## What the packet found in this repository

1. **`docs/calibration.md` rounds Clopper–Pearson bounds in the unsafe direction.** Found by the T5 referee; checked by
   the lead.
   - The round-1 and round-2 detection lower bound 0.3976 is printed as 0.40 and 0.398. Both are above the true value, so
     neither is a lower bound.
   - The 0/2 upper bound 0.8419 is printed as 0.84, below the true value, so it is not an upper bound.
   - The pooled 8/8 lower bound 0.6306 is printed as 0.631 (above the true value), and the pooled 0/4 upper bound 0.6024
     as 0.60 and 0.602 (below it).
   - The running table now gives outward-rounded values. A dated note records the correction. The pre-registered and
     scored sections are left as they were.
   - The miss-rate reading ("below 37%") was already correct, since 1 − 0.6306 = 0.369.
2. **The 1f7d041 replay is effectively a replay of the target.** The packet stressed that the replay ran at 1f7d041, not
   at 24a68cc. Between those commits no `.lean` file, stamp, challenge or comparator configuration changed; only the
   version string in `lakefile.toml` did (0.4.0 to 0.5.0). Checked by the lead with `git diff`. This changes no status.
3. **`review/README.md`'s index of answers files had stopped at 2026-11-10.** Brought up to date.

## Process deviations (disclosed)

- **Lessons 16: the lead wrote into the tree while referees read it.** The lead's check script stood untracked in
  `numerics/review/` from 21:59:16Z to 22:01:31Z, while all four referees were running. It was then parked outside the
  tree until they finished.
  - It contains the lead's conclusions about T8 numbers, not Archive 3 material.
  - The proof, triage and T5 referees list the repository files they read, and the script is not among them.
  - Asked afterwards, all four referees said they did not see it, citing the commands they ran:
    - Two of them ran `git status --short`, which printed nothing. The path is not gitignored, so those runs fell outside the
      window.
    - The blind statement referee ran one recursive grep over `*.py` for strings that the script contains. The script
      was not in its output, so the file was absent when that search ran.
- **Lessons 46: no referee report is reproduced.** Every finding above is the lead's restatement.

## AI-use disclosure

- The packet was produced with ChatGPT (GPT-6 Astra Pro), as the packet states. Its own audits share that model family.
- The lead and all four referees are Claude instances. Agreement between them is not independent confirmation.
- Nothing here is machine-checked except the lead's elaboration of a repaired copy of the draft statements, which proves
  no statement.
