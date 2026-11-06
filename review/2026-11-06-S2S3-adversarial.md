<!-- Adversarial review of S2.1, S2.2, S3 (fresh-context agent). Prompt: review/prompts/S2S3-adversarial.md. Read commit c355ee7. Verbatim final report from the agent's hand-back call. -->

c355ee7a720e36e729f4fc484eca0740d2a9e782

# Adversarial review: S2.1, S2.2, S3 at HEAD c355ee7 (clean tree)

## Verdict

**I found no BLOCKER against the mathematics or the final kernel evidence.**

- **The theorems hold.**
  - `OscInt.nonStationary`, `OscInt.stationaryPhase` and `OscInt.fold` exist.
  - Their types are syntactically the frozen statement constants.
  - `#print axioms` gives only {propext, Classical.choice, Quot.sound}. I re-ran this at HEAD with `lake build --no-build`: all targets up to date.
- **The challenge and statements are the stamped ones.** The hashes of `Challenge/StationaryPhase.lean`, `comparator-S2S3.json` and `OscInt/Statements/StationaryPhase.lean` equal stamp `20261105T234456Z-533ae0272521`.
- **The recorded evidence covers this tree.** No `.lean` file changed between 1e6c73f (verify-all, comparator PASS) and HEAD.

**One loophole in the per-step checks is MAJOR.** The guard, axiom audit and type check together can be passed by a proof of `False` that reports no axioms (finding 1). Only the kernel replay and the comparator catch it. They did run and pass, so the current claim stands on them alone.

**The claim is not yet supported by the repository's own definition (finding 2).** The S2/S3 post-proof review is missing. The prose still says "not started", so it understates rather than overclaims.

## Probes I ran (scratch only, `/tmp/adv2/`, `nice -n 10`, one Lean process at a time)

| File | What it shows | Result |
|---|---|---|
| `/tmp/adv2/probe.lean` | Axioms of the three theorems; `OscInt.fold : FoldStatement`. | Clean. |
| same | Bite test, explicit S3 instance: fold `k₁³+k₂²` on `closedBall 0 1`, `K' = {0}`. | `∃ C, ∀ A M m, … ≤ C*M*m^(-5/6)` derived from `OscInt.fold`. |
| same | Bite test, S2.1 with unbounded `p`: `Ψ = 0`, every `p` with `|p| ≥ 1`, `N = 3`. | Uniform `C*M/m^3` bound derived. |
| `/tmp/adv2/cusp.lean` | Proves `¬ FoldOrNondeg (k₁⁴ + k₂²) 0`. | Compiles. S3 does not claim m^{-5/6} for the cusp (true rate m^{-3/4}), so `FoldOrNondeg`, `dd` and `ddd` mean what the docs say. |
| `/tmp/adv2/fam.lean` | `FamilyCk n (fun σ : Icc 0 1 => fun k => σ * f k + g k)` for any Cⁿ `f`, `g`. | Compiles. The family hypothesis is met by genuinely varying families over a non-discrete compact space; the in-repo sanity theorems only use `Unit` families. |
| `/tmp/adv2/runtac.lean`, `/tmp/adv2/fakeroot/` | The loophole in finding 1. | See finding 1. |

## Statement analysis (attack 1)

**`AmpBound`.**
- The j = 0 clause forces M ≥ 0 (proved in `Assembly.lean`, `ampBound_nonneg`), so there is no sign trick.
- The integrand is continuous with compact support, so Lean's value 0 for non-integrable integrands is never reached.
- `n : ℕ` is coerced, so this is not the `⊤ = ω` (analytic) trap.

**`FamilyCk`.** Joint continuity of `iteratedFDeriv` into the operator-norm topology. Satisfiable non-trivially (`fam.lean`).

**Quantifier order.** `∃ C` comes after the family, K, K′, c, N and before A, M, σ, p, m. This matches `docs/statements.md`.

**Ill-conditioned regimes.**
- *Hessian eigenvalue → 0 across the family, or the fold condition degenerating in the limit:* impossible to hide. Λ is compact and the hypothesis holds at every σ, including limit points. For example σk₁² + k₁³ + k₂², σ ∈ [0,1], satisfies `FoldOrNondeg` everywhere, and uniform m^{-5/6} is correct there.
- *Critical points at ∂K:* covered by the hypothesis. Bad points outside K are at positive distance by compactness.
- *|p| → ∞ in S2.1:* uniform. Lean does the N1 rescaling (`LocalCrit.lean:304`, `nonStationary_of`), as in `docs/proof-S2S3.md`.

**Conventions.** `-(5:ℝ)/6` is −5/6, and `C * M / m ^ N` parses as (C·M)/m^N.

**Lean route vs `docs/proof-S2S3.md`.** They match: R1 via `familyAddLinear`, R2, L1, L2 to L6, N1/N2, F3.

## Findings

### MAJOR 1. The guard, axiom audit and type check do not detect a proof of `False`

- **Where:** `tools/src/bin/guard.rs:14-18` (FORBIDDEN list), `:135-137` (import check); `Axioms.lean`.
- **Failure scenario** (`/tmp/adv2/runtac.lean`):
  - Under `import Mathlib`, a file with `open Lean Elab Tactic in theorem carrier : True := by run_tac do …` calls `addDecl` on a theorem `carrier.bad : False` with value `True.intro`.
  - It runs under `withOptions` with `debug.skipKernelTC` set. The option name is built from strings, so the forbidden token never appears in the source.
  - `#print axioms carrier.bad` and `#print axioms oops` (for `theorem oops : False := carrier.bad`) both say "does not depend on any axioms".
  - `tools/target/release/guard /tmp/adv2/fakeroot` passes: `0 violations`.
  - The guard forbids neither `run_tac` nor `open Lean`/`Lean.`-qualified code; it only rejects `import Lean`, and Mathlib imports Lean's metaprogramming library anyway.
  - `carrier.bad` has no declaration range, so `Axioms.lean` does not enumerate it, and the guard does not count it. The theorem counts still match, so `make lean` would pass.
- **What still catches it:** only `leanchecker` per module, the export kernels, and `lake comparator --paranoid`.
- **Consequences:**
  - Every intermediate "lead-verified (module build, guard, `#print axioms`, type)" in commits 844471c through fe94504 and in `docs/HANDOFF.md` is not evidence against an agent that uses this loophole.
  - The answer to "could a false Blueprint interface have been proved?" is: yes at the lead-verification level, no at the final level.
  - Current tree: `grep` finds no `run_tac`, `Elab`, `open Lean`, `set_option` or `attribute` in `OscInt/` or `Blueprint/`. The 1e6c73f/63ff52b replay and comparator cover every audited theorem's dependency closure. So the S2/S3 claim stands, but only on those two steps.
- **Fix:**
  - Add `run_tac`, `by_elab`, `open Lean`, `Lean.` identifiers, `withOptions`, `addDecl`, `set_option` and `attribute` to the guard.
  - Include per-module `leanchecker` in "lead-verified".
  - State in the README and the `Axioms.lean` header that the audit is not independent of kernel replay.

### MAJOR 2. By the repository's own definition, the claim is not yet supported

- **Where:** `docs/STATUS.md:3-4` and rows 9-11; `review/`.
- **Failure scenario:**
  - STATUS requires every row of the trust chain, including the post-proof blind review. `review/` has no S2S3 post-proof report; only the prompt exists.
  - No single `verify-all` PASS exists:
    - On 1e6c73f the result was FAIL, because the root `leanchecker OscInt` run was OOM-killed.
    - On 63ff52b only the replay step was re-run (PASS).
    - The HEAD tools (`replay.rs` no longer checks the root module; the guard allows only imports in `OscInt.lean`) have never been through a full `verify-all`.
- **Fix:**
  - Run `make verify-all` on HEAD (or later) to one PASS record.
  - Record the post-proof reviews and this adversarial review.
  - Only then change the status.

### MINOR 3. Prose is stale and understates

| File:line | Says | Reality |
|---|---|---|
| `README.md:13-14` | S2, S3 "not started" | Proved. |
| `docs/STATUS.md:9-11` | Proof "—"; Lean column names the statement constants, not the theorems | Theorems exist. |
| `docs/HANDOFF.md:16,27` | Parts "being proved"; "Not yet: … final theorems" | Done. |
| `docs/HANDOFF.md:3` | "12 entries" | `docs/lessons.md` has 14. |
| `docs/proof-S2S3.md:3` | "not yet refereed" | It was refereed, and `Final.lean` says so. |
| `docs/statements.md:89` | "PLAUSIBLE, not yet checked by a referee" | The proof is done. |

Fix: update all of these when the status changes. Do not edit the stamped text; add dated clarifications as was done for S1.

### MINOR 4. `stamps/pins.txt` first-match semantics contradict the documented procedure

- **Where:** `stamps/pins.txt:4`; `tools/src/bin/commit.rs:98`; `tools/src/bin/challenge.rs:115`.
- **Failure scenario:**
  - `pins.txt:4` says a changed statement gets "a new pin line here (never an edit of an old one)".
  - Both tools use `find_map`, so the first (old) line wins.
  - After a re-stamp, `make commit` fails against the old stamp, and the comparator judges the old challenge export. This fails safe but blocks the documented workflow.
- **Fix:** take the last matching line, or reject duplicate keys, and add a test.

### MINOR 5. The comparator config file is not hash-checked at check time

- **Where:** `tools/src/bin/challenge.rs:76-96`.
- **Failure scenario:**
  - `comparator-S2S3.json` is in the stamp manifest (line 29; it currently matches), but `check` never compares the working-tree config with it.
  - `permitted_axioms` are not part of the export hash. An edit that widens them (for example adding `sorryAx`) would be accepted by this step.
  - This is mitigated by the independent axiom checks in `audit.rs` and `replay.rs`.
- **Fix:** require `sha256(config)` to equal the pinned manifest's line.

### MINOR 6. Per-module replay omits the Blueprint modules

- **Where:** `tools/src/bin/replay.rs:25-44`.
- **Failure scenario:**
  - `walk(root/OscInt)` skips `Blueprint/*.lean`.
  - The dropped root run was the only per-module check that reached them.
  - Blueprint declarations are kernel-checked only when reachable from an audited theorem, through the export. This suffices for the final claim, but a bogus declaration in Blueprint that is not reachable is never checked (relevant given finding 1).
- **Fix:** add the `Blueprint` modules to `modules()`.

### MINOR 7. `stamp-verify` checks only the latest stamp

- **Where:** `Makefile:8,47`.
- **Failure scenario:** the S1 stamp `20261105T203058Z-7516eb518dce`, which is still pinned, is no longer re-verified by `verify-all`.
- **Fix:** verify every stamp named in `pins.txt`.

### MINOR 8. The calibration does not cover S2/S3-style statements, and the adopted bite rule was not applied

- **Where:** `docs/calibration.md:68-74`; `OscInt/Statements/StationaryPhase.lean` (sanity section).
- **Failure scenario:**
  - Round 1 used short S1 statements with explicit constants. Its own "Not tested" list includes long statements.
  - The S2/S3 FAITHFUL ×3 verdicts in `docs/STATUS.md` carry no such caveat.
  - The rule adopted after round 1 ("bite check where it is cheap") is not applied: the sanity theorems only witness satisfiability, and only with `Unit` families.
- **Fix:**
  - Add the caveat in STATUS.
  - Add bite and exclusion theorems like `/tmp/adv2/cusp.lean` (cusp excluded) and `/tmp/adv2/fam.lean` (varying family), or the explicit instances in `/tmp/adv2/probe.lean`.

### MINOR 9. The S3 hypothesis is stronger than needed and its justification is incomplete

- **Where:** `OscInt/Statements/StationaryPhase.lean`, `FoldStatement`; `docs/statements.md:98`.
- **Failure scenario:**
  - `FoldOrNondeg` is required at every k ∈ K, independently of p, including non-critical points.
  - So S3 excludes, for example, Ψ = k₁³ + k₂³ + k₁ with K ∋ 0. It has no critical point at all, yet its Hessian vanishes at 0.
  - S2.2, by contrast, imposes its condition only at critical points for p ∈ K′.
  - `docs/statements.md:98` justifies "every point of K vs supp A", not "every point vs critical points".
  - This is not a falsity, and the S4 use (D4 cubics on an annulus) satisfies it.
- **Fix:** document the choice explicitly. Optionally weaken the hypothesis to critical points of Ψ_σ + p· for p ∈ K′, but that would need a new stamp.

### NIT 10. Projection exclusion in the audit is sound but should say so

- **Where:** `Axioms.lean` header.
- **Assessment:**
  - Projections generated by `structure` are `Expr.proj` terms and carry no axioms.
  - The only way to register a fake projection is metaprogramming (finding 1).
  - Any hidden theorem used by a final theorem still shows in that theorem's transitive axioms, and in the comparator.
  - So the exclusion cannot hide axioms from the final theorems.
- **Fix:** state this argument in the header.

### NIT 11. The S3 docstring could be clearer

- **Where:** `docs/statements.md` (S3 docstring).
- **Issue:** "Hessian nonzero" in the rank-one branch is written as `∃ v w, dd ≠ 0`. That is correct, but not visibly "rank one" until combined with `hessDet = 0`, which the disjunction supplies.
- **Fix:** one clarifying sentence.

I did not edit the repository, git state or `build/`, and did not run any `make` target.