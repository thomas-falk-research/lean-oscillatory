<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batches A5U and LOC2: the owed plants A-2 and L-i, with compiled witnesses (2026-11-28, session 17)

Appended evidence. The plant ledgers of the two batches (`docs/replay/plants/2026-11-28-A5U/`,
`docs/replay/plants/2026-11-28-LOC2/`) are records and are not edited. Findings A-1 and A-2 of
`review/2026-11-28-SPLN-A5U-LOC2-preproof-answers.md` owed two plants with compiled witnesses: a refutation of a
smaller LOC2 factor (A-1) and the A5U statement with `∃ C` moved after `∀ α` (A-2). This directory holds them.

**Who and when.** Written in scratch by an agent of the lead's model family (launched 16:50:32Z, brief SHA-256
86e50ff2ecb987456b4de58f8dd07a791a0ba6354683b622efe043b346ca72a5; Lean only through the session lock, against the
repository's build; no git, nothing written in the tree). Its run: 17:08:59Z to 17:09:26Z (`SUMMARY.txt`, script
`run.sh.txt`). The lead re-checked by script: the `ok-` files are byte-identical to the ledgers' `ok-A-e.lean.txt`
(A5U) and `ok-L-i.lean.txt` (LOC2), and `plant-L-i.lean.txt` to the LOC2 ledger's; each `plant-` file differs from its
`ok-` file in the planted definition only; each witness restates the planted definition byte-identically; no file
contains a forbidden token of the guard or a `set_option`. The lead re-compiled both witnesses in a fresh scratch
directory (17:11:43Z to 17:11:52Z): exit 0, every `#print axioms` `[propext, Classical.choice, Quot.sound]`. Inputs:
`OscInt/Statements/TriangularCrossover.lean` 0b7f8c31…, `OscInt/Front/TriangularCrossoverSanity.lean` 9332d30c…,
`OscInt/Statements/TorusLocalizationC2.lean` 9310e875…, `OscInt/Front/TorusLocalizationC2Sanity.lean` 03146e86… (the
hashes the ledgers quote).

## Outcome

| plant | mutation | outcome | evidence |
|---|---|---|---|
| A-2 | A5U with `∃ C` after `∀ α`: `∃ r > 0, ∀ α, \|α − a₀\| ≤ r → ∃ C, ∀ t n, …` | TRUE WEAKENING | `witness_A_2`: the frozen statement implies it. `witness_A_2_triU`: K2-U alone implies it with `r = a*/2` (at `α = a₀` the rate is 2/3 and the envelope 1; at `α ≠ a₀` in the window the rate is 3/4 and `t^{−3/4} ≤ t^{−2/3} E(ε t^{1/3})` for `t ≥ 1`, `0 < ε < 1`). `witness_A_2_proved`: the moved form from the proved `OscInt.API.triDecayUpper`. So the moved form is already a theorem; A5U's content is the uniformity of `C` in `α` (and, by A-f of the ledger, `r > 0`). |
| L-i | LOC2: factor `4` of `locConstC2` ↦ `1/8` | **DETECTED** | `witness_L_i : ¬ P_TorusLocalizationC2Statement`, from the LOC2 sanity module alone (no proof of K2-FQ used). Datum: `χ(k) = f(k₁) f(k₂)`, `f(x) = (9 − x²)₊³` (`C²`, support `[−3, 3]² ⊂ (−π, π)²`), zero phase, `t = 0`, `p = 0`, `B = (2π)²`. The derivatives are computed in Lean; the four integrals exactly: `∫f = 69984/35`, `∫f² = 1088391168/1001`, `∫f′² = 181398528/385`, `∫f″² = 20155392/35`. Left side `(69984/35)² ≈ 3.998·10⁶`; the planted right side is below `3.66·10⁶`. The same datum refutes every factor below about 0.137, so the explicit constant of K2-FQ is now pinned from below, within a factor of about 29 of the proved 4. |

The planted copies are also rejected by the copied sanity scripts (`plant-A-2`: six theorems, where
`obtain ⟨r, hr, C, hC⟩` no longer destructs; `plant-L-i`: `P_loc2_locConstC2_const`, as in the LOC2 ledger), which is
recorded and not counted as detection.

**Effect on the ledgers.** LOC2: L-i moves from NOT DETECTED to DETECTED (compiled witness); the other NOT DETECTED
entries (L-c, L-e, L-f, L-j, L-k) are unchanged. A5U: A-2 is a sixth TRUE WEAKENING next to A-e, A-f, A-h, A-k, A-l.

## Files (SHA-256)

| file | SHA-256 |
|---|---|
| `ok-A-2.lean.txt` | `4da66cedb15956602668053503ddb5895cb78f66d62ba2f10f82c92935a44e5f` |
| `ok-A-2.out` | `0dffe055047af05d6767339d45236d4997289e65d8db4f4181eb6f291124fd3a` |
| `plant-A-2.lean.txt` | `c31d2734b05d8459cc86d14201a782704c42e634f8ef84c4a2951f67f843d219` |
| `plant-A-2.out` | `07a6da32eaf2f28b854b6a33cab57c257b383dd10be6e8345ba733796fe2e2c9` |
| `witness-A-2.lean.txt` | `06c6099179ac71f82800d149d7b19961bc9dd7c9d31ffa89f65431b9dbb3ce39` |
| `witness-A-2.out` | `d59937061aec2a9fbf980cc9ee0c11017b1b9b9a0b137f39c2a62cf8b35ee7b5` |
| `ok-L-i.lean.txt` | `751f21e3a07a900c3a01b925fb7baea6ab2382b97e2cad0a5287947106feb900` |
| `ok-L-i.out` | `0dffe055047af05d6767339d45236d4997289e65d8db4f4181eb6f291124fd3a` |
| `plant-L-i.lean.txt` | `f6eec5b1035024c88b66c2f5fb98bc8397703bb2e6b08aee58401cc52796354f` |
| `plant-L-i.out` | `b330142c53a38006371ba609dae96fb07d541a9823a5bc2b85fcfd338d5ff1e2` |
| `witness-L-i.lean.txt` | `9cd22ba4adc152c198f2568e14244e9922c47a92280b33280b29c8bc238bcdbf` |
| `witness-L-i.out` | `f986f6587d794ffc56e6ca47d74a0cbbf6c46060c665a46eca0bf79fe912d412` |
| `SUMMARY.txt` | `c6eed6c852d60e305d14eddf5f50d4b66f2ce2c837f2ac3ad6442b47597e48c2` |
| `run.sh.txt` | `f0b4f94342bdbe638125ce8a06704db19ce2d2114bccd1906ba0b915745ee689` |

To re-run a witness: copy it to a `.lean` file outside the repository and, from the repository root after
`lake build`, run `lake env lean -DautoImplicit=false <file>`.
