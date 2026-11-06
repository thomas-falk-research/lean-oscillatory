# Lead's answers to the S2/S3 pre-proof reviews (2026-11-05)

Verdicts: referees A and B independently FAITHFUL ×3 against `docs/statements.md` and TRUE classically; no
BLOCKER, no MAJOR. Pinned to the commitments of stamp `20261105T234456Z-533ae0272521`.

- A MINOR (S3 condition imposed at every point of K, not only at critical points): accepted as a documented
  restriction; the intended consumer S4 satisfies it everywhere on its annuli (the Hessian of a binary cubic with
  Disc < 0 vanishes only at 0, and where its determinant vanishes it has rank one with the cubic nonzero along the
  kernel).
- B MINOR (the reduced curve (x, y*(x)) can leave K): accepted as a proof obligation; `docs/proof-S2S3.md` now says
  that every local step works on a neighbourhood of (τ₀, k₀) obtained by continuity from the hypothesis at the
  single point k₀ ∈ K, so no hypothesis outside K is used.
- NITs (`Λ : Type` is universe 0; S2.2 single phase; uniformity over all p would also hold in S3; GradLower on K):
  accepted as stated; universe 0 suffices for every planned use (Λ = [0, ε₀] and finite products with compact
  subsets of ℝ²).
- Both referees independently confirm C² amplitude regularity for S2.2 (Hörmander, ALPDO I, Thm 7.7.5, k = 1,
  phase C⁴) and give the same route for S3; the C² claim for S3 is upgraded from PLAUSIBLE to "argued by two
  independent referees", still not proved.
