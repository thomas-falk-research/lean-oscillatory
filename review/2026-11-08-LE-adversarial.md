72188111a02485940fffd2788bc90c10ac4be5f6

# Adversarial review: batch LE, session-7 tool changes, session-7 records

**Verdict: no BLOCKER and no MAJOR.** I could not break any of the six claims (a)–(f). They hold as stated, with the qualifications in the findings below: 6 MINOR and 9 NIT. Nothing was written in the repository. I worked in `/tmp/advLE/` (a clone at `/tmp/advLE/repo` for the stamp and numerics runs) and ran one Lean process at a time under `nice -n 10`. `git status` stayed clean throughout.

## What I re-ran and checked
- **Axioms.** `#print axioms` on `OscInt.API.latticeKernel1Explicit`, `latticeKernelFactor` and `latticeLaplacianExplicit` shows only propext, Classical.choice and Quot.sound. I also checked that T6E implies the frozen T6 (`exact ⟨_, latticeLaplacianExplicit⟩`).
- **What changed after the replay.** `a1d2a64..HEAD` touches only the replay record and the two prompt files. `docs/replay/2026-11-08-session7-LE-verify-all.txt` is the same as `build/verify-all.log` line for line, apart from its two header lines and a blank line (RESULT PASS, EXIT 0).
- **Stamps.** `stamp verify-every`, run in the clone with the built binary: 12 directories verified, 36 RFC 3161 tokens OK, no files written. The LE statement files at HEAD hash to the values in `stamps/20261108T160847Z-4a183530559f/manifest.txt`: `OscInt/Statements/LatticeExplicit.lean`, `Global.lean`, `Challenge/LatticeExplicit.lean` and `comparator-LE.json`. The manifest at 4a18353 contains no Parts, Final or Assembly file. Only the sanity file changed later (in c91a9a8), and it is covered by the review stamp.
- **Plants.** I re-ran `plants_le.py.txt` into `/tmp/advLE/plants`. The result is exactly the record: 9 rejected, 1 blind spot accepted, 10 controls accepted.
- **Numerics.** I rebuilt and re-ran `lattice1` and `classify_vv` in the clone. Both outputs are byte-identical to `numerics/results-lattice1-2026-11-08.txt` and `numerics/results-classify-vv-2026-11-08.txt`.
- **Hash-locked CI install.** I ran both CI pip commands in a fresh venv (Python 3.13): they succeed, and `reuse lint` and `cffconvert --validate` pass. A planted extra line `tomli==2.0.1` without a hash is refused with "Hashes are required in --require-hashes mode".
- **Order (claim a).** The repository's evidence is git order plus the lead's own statement, so I checked the session transcript, which is outside the repository (`~/.claude/projects/.../f26831f6-....jsonl`):
  - The first proof text (`two_rpow_neg_half`, `lePiece2`) appears at 16:56:36.992Z, after the review stamp (16:45:19Z).
  - The file birth times agree: Parts 16:56:37, Final 16:57:29.
  - The route referee ran from 16:55:47 to 16:58:55 and the lead began the parts 50 s after launching it. This is disclosed as M1 in `docs/proof-LE.md`.
  - The committed route-referee report is verbatim.
  - The pre-proof referees' scratch (`/tmp/refereeA`, `/tmp/refereeB`) contains no proof of T0E, T6F or T6E.
- **Pre-registration order (claim c).** Both git and the transcript give the same order:
  - LE: prereg 15:35:43, amendment 1 at 15:36:16, program first written 15:36:59 and committed 15:37:07, result 15:37:43.
  - VV: prereg 16:20:32, program written 16:20:59 and committed 16:21:30, result 16:21:57.
- **Mathematics re-checked by hand:**
  - Constant algebra: 8·(t·2^{−1/2})^{−1/2} = 8·2^{1/4}·t^{−1/2}, and 18·(t·2^{−1/2})^{−1/3} = 18·2^{1/6}·t^{−1/3}. Three plus two pieces give 24·2^{1/4} and 36·2^{1/6}.
  - Thresholds: 518.5 and 1321.5. Constants: (A+B)² = 4754.05, and (A+B)/(2π·0.78575) = 13.97.
  - The angle conditions on all five pieces are correct.
  - Fubini: `setIntegral_prod_mul` needs no integrability, so there is no junk-value risk.
  - `Real.rpow`: avoided by `0 < t` and `1 ≤ t`. Had T0E allowed t < 0, Lean would give (−s)^{−1/2} = 0 and (−s)^{−1/3} = s^{−1/3}/2.
  - Clarifications 2, 8 and 9 in `docs/statements.md` (conjugation symmetry, the 2.9 factor, the 75.9 t^{−2/3} user constant) are correct.
  - The prior-art identities are correct: Cauchy–Watson, 4π²(…)² = Γ(1/3)²·48^{1/6}/√3, and the D4 points at (±π/2, ±π/2).

## BLOCKER
None.

## MAJOR
None.

## MINOR

**m1. The T6/T6L disclosure is incomplete in the front-facing records, and batch LE is missing from them.** (claim d)
- `README.md` lines 11–16 and the Batch GD status row, and `CHANGELOG.md` "Unreleased" lines 22–24, still present T6/T6L without the "classical, separable" caveat. CHANGELOG even calls Γ(1/3)²·48^{1/6}/√3 "the D4 constant", though it is the Cauchy–Watson Bessel constant. STATUS, applications and `docs/release-notes/v0.4.0.md` do carry the caveat.
- Batch LE (T0E, T6F, T6E) has no row in `docs/STATUS.md` and is absent from README and CHANGELOG. CHANGELOG still says "45 statements", but `stamps/statements.json` has 48. The session-7 tool changes (`stamp verify-every`, hash-locked CI installs) are also not in CHANGELOG.
- `docs/HANDOFF.md` lines 8–15 is stale from session 6 ("90 names"; "GD on x³ + y³" with no caveat).
- Failure scenario: a release is cut from CHANGELOG "Unreleased" without three statements and without the caveat. README readers see T6 as a showcase of GD.
- Fix:
  - Add the one-line caveat and a pointer to `docs/prior_art.md` to the README intro and the CHANGELOG GD entry.
  - Add the LE statement changes and the tool changes to CHANGELOG.
  - Add STATUS rows for LE, carrying the "content only for t > 518 / t > 1321" caveat, when the post-proof reviews land.

**m2. The disclosure does not say that no non-separable phase is instantiated for GD anywhere, and the planned acceptance model will not test the D4 branch.** (`docs/prior_art.md` lines 59–61, `docs/design/vector-amplitudes.md` lines 66–71)
- Every GD demonstration in the repository uses a separable phase: T6 (cos k₁ + cos k₂) and the consumer example x³ + y³.
- Q(3) was chosen because it has folds only. It is the near-separable regime: the c₁c₂/m term resolves the hyperbolic umbilics of cos k₁ + cos k₂ into folds. So even after batch VV, GD-C/GD (the D4 branch) will not have been exercised on a non-separable symbol. The triangular fallback T has cusps, so it is not covered.
- The documents are individually honest (they say "GD-F applies"), but nowhere is it stated that "non-separable" will be shown only for GD-F.
- Fix: say this in `docs/prior_art.md` and in the design doc's §4, and in ROADMAP item 2.

**m3. `stamp verify-every` silently skips a symlinked stamp directory.** (`tools/src/bin/stamp.rs` lines 217–221)
- `DirEntry::file_type().is_dir()` does not follow symlinks.
- Reproduced: `stamps/20991231T000000Z-symlinked -> /tmp/advLE/notastamp` gives "12 verified, 0 failed". A plain stray directory is correctly rejected.
- Git tracks symlinks, so a committed symlink under `stamps/` passes. "Every stamp directory" is not literally true.
- Fix: treat any non-regular entry other than `pins.txt`, `statements.json` and `roots/` as a failure, or follow the link with `fs::metadata` and verify it.

**m4. `verify` does not check that a manifest covers anything.** (`stamp.rs` lines 150–171)
- The manifest check verifies only the lines that happen to be present:
  - `n == 0` passes.
  - Lines whose hash is not 64 characters are skipped silently.
  - The header `OSCINT-MANIFEST 1` is not checked.
  - The file list is not compared with `git ls-tree -r <commit>`.
  - The commit is not required to be a full SHA or an ancestor of HEAD.
- Anyone can get valid RFC 3161 tokens over any bytes. So a degenerate or partial manifest with real tokens passes verify-every. For pinned statements, `commit.rs` still binds the commitments; for review stamps, nothing checks that the review files are in the manifest.
- Today's 12 directories are fine: for example, 589 hashes for 589 tracked files at 4a18353.
- Fix:
  - Require the header and a 40-hex commit that is an ancestor of HEAD.
  - Fail on any malformed line.
  - Require the hashed set to equal `git ls-tree -r --name-only <commit>`.

**m5. Claim (a), "before any Lean proof", cannot be checked by a third party.**
- RFC 3161 bounds when the statements and reviews existed, not when the proofs did not. The ordering of proofs rests on committer dates, which are self-reported.
- In this very session, cherry-picks rewrote committer dates: 69b82f4 and 68cddb1 have author dates 15:39 and 15:52 but committer date 16:16:29.
- I found the claim true from the session transcript and file birth times, but those are not in the repository.
- Fix: word the claim in `docs/proof-LE.md` and `docs/statements.md` as "by git order and the lead's session record". This is how STATUS line 141 already words it for earlier batches.

**m6. `docs/design/vector-amplitudes.md` §1 is correct in substance, with small imprecisions.** I checked the duality route in Lean.
- `exists_dual_vector''` has the stated form for RCLike 𝕜.
- The real-scalar derivative bound compiles via `(ℓ.restrictScalars ℝ).norm_iteratedFDeriv_comp_left` and `ContinuousLinearMap.norm_restrictScalars`, with `NormedSpace ℝ E` coming from `NormedSpace.complexToReal`. ℂ-linearity is still needed to pull e^{imΦ} out, and ℓ : E →L[ℂ] ℂ has it, so the "restricted to ℝ-scalars for the real derivatives" reading is right.
- All frozen bound statements I read (GD-C, GD, GD-F, GD-N, S2.1, S2.2, S3) have the form `∃ C, ∀ A M …`, as the transfer requires. Limit statements (S4.2, F2, T6L) are correctly not claimed.
- Imprecisions:
  - `integral_comp_comm` needs `k ↦ e^{imΦ k} • A k` integrable, not "A integrable".
  - The "junk value 0, bound trivial" branch also needs C·M·r ≥ 0. C ≥ 0 does follow from the scalar statement at A = 0, M = 1, but the doc does not say so.
  - Under the frozen hypotheses (ContDiff, compact tsupport) A is always integrable, so the junk branch can never occur.
  - `ContinuousLinearMap.norm_restrictScalars` is used but is not in the name list or in `MathlibNames.lean`.
- Fix: correct the integrability sentence, note that the junk branch is unreachable, and add the name.

## NIT
- **n1. Piece lengths.** `OscInt/Front/LatticeExplicitAssembly.lean` lines 13 and 29 say "five pieces of length π/2". The end pieces [−π, −3π/4] and [3π/4, π] have length π/4.
- **n2. Claim written before its evidence.** `docs/prior_art.md` line 50 says "the factorisation is machine-checked by batch LE (statement T6F)". It was written at 0a7409d (15:34), before T6F was stated or proved (16:57). It is true now.
- **n3. Plant coverage (claim b).** The record is accurate, but:
  - Only the three statement defs are mutated; `latticeKernel1` itself is never planted. A def over [0, 2π] passes `latticeKernel1_zero_zero` and `_zero_one`, and also T6F, because ξ is an integer there. For real ξ, T0E's meaning rests on reading the def.
  - There is no plant on T6E's constant, and none restricting x.
  - The T0E-int plant is rejected only because `(1/2 : ℤ)` elaborates to 0.
  - Rerunning the generator overwrote the first-run `.out` files; the first run survives only in commit 4a18353.
- **n4. OTS check can panic.** `stamp.rs` line 182: an `.ots` file of 31–33 bytes that starts with the magic panics on the slice, with exit 101. Reproduced with a 32-byte truncation: verification aborts, the remaining directories are never tried, and "each failure is reported" is broken. The run still fails, so nothing passes wrongly. Fix: check `b.len() >= OTS_MAGIC.len() + 34` first.
- **n5. Pin paths are not validated.** `pinned_dirs` does not check that a pin path starts with `stamps/` or is free of `..`. A pin to an absolute or out-of-tree path is verified there; a fresh CI checkout would catch it.
- **n6. Pre-registered check (claim c) is not discriminating against constants that are too large.** It reports as run: (a) holds at a ratio of 0.088. It would not catch a draft constant up to about 11 times too small, which would still pass. That is fine for a truth check, but say so next to "catch a wrong draft constant".
- **n7. Unpinned CI tools outside pip (claim e).** `go install actionlint@v1.7.7` (Go checksum database) and `apt-get install shellcheck` (unpinned version) are not hash-locked. Pip itself is the runner's ensurepip version.
- **n8. Q(1) reading.** Design doc §4 is right that (−π, −π) is not D4 at m = 1. All third derivatives of P contain a sine factor, so the 3-jet of ω vanishes there. But it is the band minimum with a vanishing 3-jet, so the local rate is at worst t^{−1/2}. That is worth one clause.
- **n9. Verify-all start time is reconstructed.** The replay record's start time is derived from the wall time, and "alone on the machine" is not evidenced in the log. Fix: log `date -u` at start and end.

## On the specific attack points
- **Junk values:** checked; none bite (see the Mathematics bullet).
- **Constant algebra and the five-piece split:** both correct (only the n1 wording is off).
- **Fubini:** `setIntegral_prod_mul` needs only SFinite, so no integrability is needed.
- **Quantifier order:** the constants are explicit and sit outside ∀ t ξ / ∀ t x.
- **"Explicit constant": useful?** The answer is "only for t > 518 (1D) and t > 1321 (2D), and about 195 times the Landau value squared". This is said in `docs/statements.md` (clarification 6, item 3), in the API annotations and in the Final.lean docstring. It is not yet said in README, STATUS or CHANGELOG, because LE is absent from them (m1).
- **QWZ classification:** read correctly.
  - P = 2 + m² + 2m(c₁+c₂) + 2c₁c₂ = |d|² checked; the gap condition m ∉ {0, ±2} checked; min P = 1, 0.25, 1 checked.
  - Q(3): no Hessian-zero point, minfold 0.158.
  - S trap: 3434 X points. T: 6 cusps.
  - "m = 3 is topologically trivial" is disclosed.
