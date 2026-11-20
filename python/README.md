<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->
# oscint_cert (experimental, version 0.2.1; not published)

OscInt is a Lean 4 library of machine-checked estimates for oscillatory integrals; a *statement* is one of its frozen,
proved propositions. This package evaluates a few of those statements at given numbers and writes the result as a
*certificate*; its `check` command is the one program that may call a certificate CERTIFIED. The contract, with every
definition, is `docs/contract/certificate-v0.md`. Standard library only; Python 3.11 or later.

```bash
cd python
python3 -m oscint_cert kinds
python3 -m oscint_cert make lattice-envelope --inputs '{"d": 1, "t": "2"}' --statements ../stamps/statements.json > cert.json
python3 -m oscint_cert check cert.json --statements ../stamps/statements.json \
  --expect-statements-sha256 "$(sha256sum ../stamps/statements.json | cut -d' ' -f1)"
python3 -m unittest -v tests.test_cert      # differential tests need python-flint
```

A verdict is only as good as the statement list given to `check`. The line above pins the list to the copy in this
checkout; someone who received a certificate and a verdict from elsewhere pins it to the hash in the release notes of
the release they trust. The verdict records the hash (`statements_sha256`), whether it was pinned
(`statements_pinned`) and the hash of the certificate it is about (`certificate_sha256`).

Numbers go in as strings holding exact rationals (`"7/2"`, `"0.25"`) and come out as enclosures `{"lo", "hi"}` whose
ends are fractions such as `"16849268938195967658308169841/500000000000000000000000000000"`; convert them with exact
rational arithmetic (Python: `fractions.Fraction(text)`). `--digits` (10 to 200, default 30) sets the working
precision of `make` and `check`; use the same value for both.

## A worked example: your own phase

Is `|ω″| ≥ 4/5` on `[−1/2, 1/2]` for `ω(k) = cos k`, and what does the machine-checked second-derivative bound give
for `|∫_{−1/2}^{1/2} e^{i(100·ω(k) + ξk)} dk|`, every real ξ?

```bash
python3 -m oscint_cert make vdc-hypothesis --statements ../stamps/statements.json \
  --inputs '{"phase": [{"amp": "1", "freq": 1, "fn": "cos"}], "order": 2, "a": "-1/2", "b": "1/2", "mu": "4/5", "t": "100"}' > cert.json
python3 -m oscint_cert check cert.json --statements ../stamps/statements.json
```

`check` answers CERTIFIED (exit code 0) with `"hypothesis": {"status": "PASS", …}` and a `recomputed` enclosure of
`8·80^{−1/2} = 0.8944…`. That is below the trivial bound `b − a = 1`, so here the statement says something.

With `"mu": "9/10"` the hypothesis is false (`|ω″(k)| = cos k` is 0.8776 at the ends). `make` then writes no
certificate: it exits with code 3 and names a point on standard error (`"point": "15/32"`). To see the checker refuse
a false certificate, change `"4/5"` to `"9/10"` by hand in `cert.json` and run `check` again: REJECTED, exit code 1,
with the same point under `hypothesis`.

## What the kinds mean

| Kind | Quantity | Read it as |
|---|---|---|
| `bessel-j` | `J_n(x)` | a certified Bessel value; no statement involved |
| `lattice-population` | `J_n(2t)²` | the probability at site n at time t, one excitation started at site 0 of an infinite chain, time in units of ħ/(hopping amplitude) |
| `lattice-envelope` | `min{1, (C*/2π)^d (2\|t\|)^{−d/3}}` | a bound for the **amplitude** at every site of ℤ^d for a datum of ℓ¹ norm 1; the probability is bounded by its square |
| `vdc-hypothesis` | `(5·2^{k−1} − 2)(t·mu)^{−1/k}` | a bound for `\|∫_a^b e^{i(tω(k) + ξk)} dk\|` once `\|ω^{(k)}\| ≥ mu` on [a, b] has been certified |

Exit codes: `check` 0 CERTIFIED, 1 REJECTED, 2 UNRESOLVED, each with a verdict on standard output; 3 for anything
that is not a verdict (command line, unreadable file, unusable or unexpected statement list). `make`: 0 with a
certificate, otherwise 3 with a message. UNRESOLVED means the checker could not decide within its limits (contract,
section 4); it is never a rounded answer. The slowest inputs the limits allow (a Bessel argument near 400 written with
100 digits) took 32 s to 76 s in the lead's test; ordinary inputs take well under a second.
