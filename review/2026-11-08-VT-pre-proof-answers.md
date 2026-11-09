# Answers to the VT pre-proof reviews (lead, 2026-11-09, before any proof of a VT statement)

Reports at 76cdff1: `review/2026-11-08-VT-pre-proof-A.md`, `review/2026-11-08-VT-pre-proof-B.md`. Both: FAITHFUL and
TRUE on all four statements; the vector texts are character for character the scalar ones up to the E binder and `•`
(both checked by script); every step of the duality route exists at the pin with the needed signature; no BLOCKER, no
MAJOR. No statement text changes.

## Referee A
- **MINOR-1 (universe restriction).** Documented (clarification 7); a universe-polymorphic transfer theorem is planned with
  the proofs, as an ordinary theorem, not a frozen statement.
- **MINOR-2 (the 'C after E' blind spot is overstated).** Agreed: the two placements are equivalent via duality
  (clarification 5). The sanity file now has `globalNondeg_uniform_dim` (one constant for all ℂⁿ), against which the plant
  cannot succeed by instantiation; record updated (second run).
- **MINOR-3 (matrices need a local instance).** Clarification 6.
- **NIT-1 (integrability reason).** Clarification 4. **NIT-2 (GD-C-V only at E = ℂ).** `globalDecayCrit_pair` added.
  **NIT-3.** Clarification 5.

## Referee B
- **MINOR-1 (no infinite-dimensional datum; FiniteDimensional plant accepted, verified).** Fixed: `globalNondeg_bounded`
  (E = ℕ →ᵇ ℂ); the FiniteDimensional plant is now rejected (second run).
- **MINOR-2 (uniformity tested only by tactic order).** Fixed by `globalNondeg_uniform_dim`, as for A MINOR-2.
- **NIT-1 (matrices), NIT-2 (universes), NIT-3 (real spaces).** Clarifications 6, 7.
- **NIT-4 (plant name 'findim' did not match its mutation).** Renamed 'subsingleton' in the second run; the real
  FiniteDimensional plant added.
