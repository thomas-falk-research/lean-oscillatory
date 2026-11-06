<!-- Post-proof fidelity review of S1 by a fresh-context agent (model output, not a human referee).
Prompt: review/prompts/S1-post-proof.md (sha256 0b59d23d0619d549bed48bf8675a144585914d9987f892e216fd496a89fc7d62).
Read: commit 402e92a. Report reproduced verbatim below the rule; the lead's answers follow it. -->

---

# S1 (van der Corput) post-proof fidelity review: report

**Bottom line:** I found no BLOCKER or MAJOR issue. All three final theorems prove exactly the frozen statements that were reviewed before the proofs. Those statements are faithful to `docs/statements.md` S1. The commitments that `make commit` produces now are byte-identical to the stamped ones.

The prompt's sha256 matched `0b59d23d…7fc62`. I wrote nothing to the repository except what `make commit` writes under `build/`, and `git status` is clean.

## Commands run (verbatim results)

**1. `git rev-parse HEAD`**
```
402e92a5224806d5014cf66c19fc5f1ff87f3f43
```

**2. `nice -n 10 lake env lean StatementTypes.lean`**
```
TYPE-OK OscInt.vanDerCorput_one : OscInt.Statements.VdC1Statement
TYPE-OK OscInt.vanDerCorput_two : OscInt.Statements.VdC2Statement
TYPE-OK OscInt.vanDerCorput_three : OscInt.Statements.VdC3Statement
```
This check compares the `Expr` of each theorem's type with the statement constant itself, with no unfolding.

**3. `nice -n 10 make commit`, then `cat build/commit/commitments.txt`**
- The build completed (2820 jobs), with only warnings that the module system is not used.
- The axiom audit printed "36 of 36 theorems clean". The TYPE-OK lines were printed again, and `build/skipped/` is empty.

```
a837c8bd8352929aa4ba6456ff19603cd34f7ae09b2896de0af2565fd0f803b4  OscInt.Statements.VdC1Statement
66cc331de7d7bf5fb38076895ff7014f280b41cced6492f70cd87134a78a39f5  OscInt.Statements.VdC2Statement
30b3f96ca215778d4034c6ca660818b04a842bb4b574f27f4a648a64bf9ab4f4  OscInt.Statements.VdC3Statement
```
These match the three `commitment` lines of `stamps/20261105T203058Z-7516eb518dce/manifest.txt` exactly. They are also the hashes the pre-proof review was pinned to.

**4. `nice -n 10 lake env lean Axioms.lean | grep -E 'vanDerCorput|AUDIT-TOTAL'`**
```
AUDIT OscInt.vanDerCorput_one propext,Classical.choice,Quot.sound
AUDIT OscInt.vanDerCorput_three propext,Classical.choice,Quot.sound
AUDIT OscInt.vanDerCorput_two propext,Classical.choice,Quot.sound
AUDIT-TOTAL 36 36
```

## Other checks
- **Files unchanged since the stamp (sha256 equal to the manifest):** `OscInt/Statements/VanDerCorput.lean` (7cda5a99…), `docs/statements.md` (9a6f229b…), `comparator.json`, `Challenge/VanDerCorput.lean`, `Axioms.lean`, `Makefile`, and the lakefile, toolchain and manifest.
- **Files changed since the stamp commit 7516eb5:**
  - `StatementTypes.lean`: only the three `#assert_type_is` lines were added.
  - `tools/src/bin/stamp.rs`: one line, `let _ = fs::remove_file(&tsq);`. This only affects creating stamps, not checking statements.
  - New proof files and docs.
- **`comparator.json`:** it names exactly the three theorems, and the permitted axioms are {propext, Quot.sound, Classical.choice}. I did not run the comparator; the prompt does not ask for it.
- **Proof files:** I grepped all of `OscInt/VanDerCorput/*.lean` (Final, Assembly, Split, One, Amplitude, Higher) and found:
  - no `axiom`, `opaque`, `unsafe`, `implemented_by` or `extern`;
  - no `instance`, `notation`, `macro`, `syntax` or `elab`;
  - no `attribute`, `set_option` or `def`/`abbrev`;
  - nothing that reopens the namespace `OscInt.Statements`. They only `open` it.
- **`Final.lean`:** it states each theorem with the statement constant as its type, which `StatementTypes` confirms.
- Given the `Expr`-equality type check, the equal commitments and the clean axiom audit, nothing in the proof files can change what the statements mean.

## Verdicts

All three verdicts are scope `full` and are pinned to the commitment hashes above.

**`OscInt.vanDerCorput_one`** (commitment `a837c8bd…f803b4`)
- **Against docs S1.1: FAITHFUL.** Every hypothesis matches:
  - `HasDerivOn φ φ'` and `HasDerivOn φ' φ''`;
  - φ′ is `MonotoneOn ∨ AntitoneOn` on `Ioo`;
  - ν ≤ |φ′| on `Ioo`;
  - `AmplitudeOn`.
- The conclusion matches: ‖I‖ ≤ 3/ν · (‖ψ b‖ + ∫‖ψ′‖).
- **Against Stein VIII §1.2 (Prop. 2 with λ absorbed into φ, plus the Corollary, c₁ = 3): FAITHFUL-WEAKER.**
  - The Lean asks that φ′ is differentiable on (a, b) and continuous on [a, b]. Stein's argument needs only φ′ monotone, so this is a stronger hypothesis.
  - It is more general in the amplitude: ψ continuous on [a, b], differentiable on (a, b), with ψ′ integrable.
  - For Stein's setting with φ, ψ in C¹ on [a, b], the Lean statement implies Stein's.

**`OscInt.vanDerCorput_two`** (commitment `66cc331d…ab9f5`)
- **Against docs S1.2: FAITHFUL.** The phase is φ + p·x with p universal, the hypotheses are on φ alone, and the bound is 8/√μ · A.
- **Against Stein (c₂ = 8): FAITHFUL**, except for the documented endpoint-continuity choice for φ′ (the MINOR finding below).

**`OscInt.vanDerCorput_three`** (commitment `30b3f96c…ab4f4`)
- **Against docs S1.3: FAITHFUL.** It adds `HasDerivOn φ'' φ'''`, and μ ≤ |φ‴| replaces the bound on φ″. The bound is 18·μ^(−1/3) · A, using `Real.rpow` with μ > 0.
- **Against Stein (c₃ = 18): FAITHFUL**, except for the same endpoint-continuity choice for φ′ and φ″.

## Findings
- **MINOR:** in all three statements, φ′ (and φ″ in S1.3) must be continuous on the closed interval [a, b]. Stein only assumes φ smooth on (a, b). This is documented and matches the source's Cᵏ hypothesis. The excluded endpoint cases can be recovered by applying the statement on [a, d] and letting d → b: ψ is continuous on [a, b] and the integrand is integrable. Not a defect.
- **NIT:** the pre-proof review says that for k = 1, excluding a φ′ that is unbounded at an endpoint "costs nothing". Stein's hypotheses do allow φ′ → ∞ at b while φ′ stays monotone with |φ′| ≥ ν, so the exclusion does remove cases. It costs nothing in substance only because of the same subinterval-limit argument. This belongs with the MINOR finding above.
- **NIT (carried over from the pre-proof review):** the stamped file's header still says "derivatives of order < k are continuous on [a, b]". For k = 1 this is inaccurate, since φ′ itself must be continuous. `docs/statements.md` states it correctly, and the lead has deferred the fix to the next re-stamp.
- **NIT:** the variable p in S1.2 and S1.3 adds no logical strength, because φ is universally quantified. This is intended: it makes "invariant under adding a linear term" visible.
- **NIT:** `IntervalIntegrable ψ'` and "Lebesgue integrable on [a, b]" are equivalent, as agreed in the pre-proof review.

Files reviewed (all under `/home/user/lean-oscillatory/`):
- `docs/statements.md`
- `OscInt/Statements/VanDerCorput.lean`
- `OscInt/VanDerCorput/Final.lean`, plus a grep of the other proof files
- `StatementTypes.lean`
- `comparator.json`
- `Axioms.lean`
- `Makefile`
- `tools/lean/CommitEnv.lean`
- `stamps/20261105T203058Z-7516eb518dce/manifest.txt`
- `review/2026-11-05-S1-pre-proof.md`
- `build/commit/commitments.txt` (written by `make commit`)

---

## Lead's answers (2026-11-05)

- MINOR (endpoint continuity) and the NIT on "costs nothing": accepted as stated; recorded in the README and STATUS
  wording as part of what "as stated" means (hypotheses as in `docs/statements.md`, matching the source's C^k).
- NIT (header wording): fix deferred to the next re-stamp of the statement file, as answered in the pre-proof review.
- Other NITs: as answered in the pre-proof review.
- The comparator was run separately by the lead on commit 5553b78 (`make comparator`: "Your solution is okay!",
  challenge export sha256 7fe4db8d… equal to the stamped `challenge-export` line).
