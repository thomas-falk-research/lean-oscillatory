# Lead's answers to the S4.1 pre-proof reviews (2026-11-06)

Verdicts: referees A and B independently FAITHFUL to `docs/statements.md`, FAITHFUL-WEAKER than the classical D4
result, TRUE; no BLOCKER, no MAJOR. Pinned to commitment 5205ebc0… (stamp `20261106T033706Z-63564a8d78cd`).

- MINOR (both referees): `disc < 0` covers the hyperbolic umbilic D4⁺ only; the classical uniform t^{-2/3} bound holds
  for Disc ≠ 0 (also the elliptic umbilic D4⁻, e.g. x³ − 3xy², Disc = 108). The brief says "negative discriminant"
  and its limit constant Γ(1/3)²/(√3|Disc|^{1/6}) is the D4⁺ constant (checked numerically for x³ + y³ and
  x²y + y³, `numerics/results-2026-11-05.txt`), so `< 0` is faithful to the brief and kept. Widening S4.1 to `≠ 0`
  is an owner option (a new statement, stamp and review); both referees note the route covers D4⁻ (definite Hessian
  covariant, nondegenerate branch). Recorded in `docs/HANDOFF.md`.
- NITs (sanity coverage of the mixed coefficients b, c; dependence of C on φ as Disc → 0; amplitudes for every δ;
  wording of the gradient absorption y ↦ y + t∇φ(0)): accepted; the mixed-coefficient check and the wording go into a
  later sanity file (the stamped file is not edited).
