<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->
# oscint_cert (experimental, version 0.2.0; not published)

Certificates for evaluated OscInt statements and the one checker that may say CERTIFIED. The contract is
`docs/contract/certificate-v0.md`. Standard library only; Python 3.11 or later.

```bash
cd python
python3 -m oscint_cert kinds
python3 -m oscint_cert make lattice-envelope --inputs '{"d": 1, "t": "2"}' --statements ../stamps/statements.json > cert.json
python3 -m oscint_cert check cert.json --statements ../stamps/statements.json
python3 -m unittest -v tests.test_cert      # differential tests need python-flint
```

A worked example for a user's own phase: is `|ω″| ≥ 4/5` on `[−1/2, 1/2]` for `ω(k) = cos k`, and what does the
machine-checked second-derivative bound give at `t = 100`?

```bash
python3 -m oscint_cert make vdc-hypothesis --statements ../stamps/statements.json \
  --inputs '{"phase": [{"amp": "1", "freq": 1, "fn": "cos"}], "order": 2, "a": "-1/2", "b": "1/2", "mu": "4/5", "t": "100"}'
```

The answer is a certificate whose bound encloses `8·80^{−1/2} = 0.8944…`; `check` then answers CERTIFIED with the
hypothesis status PASS, or REJECTED with a point where the hypothesis fails if `mu` is raised to `9/10`.
