09e4bc72c1a931cb5563e70b22f403373cb00d92

# Adversarial review: batch VT and the QWZ finding

I left the repository, git state and `build/` untouched; `git status --porcelain` is empty. All scratch files are in /tmp/advVT/. I ran one Lean process at a time, with nice -n 10.

## Summary
- **(a) The proof claims hold.**
  - The statement and challenge files match the RFC 3161–stamped manifest (`784ca9a5…`, `5b0ec1be…`).
  - The `.tsr` imprints equal the sha256 of each manifest. The times are 23:54:21Z and 00:24:23Z.
  - The review-stamp tree contains no VectorParts, VectorFinal or Blueprint/Vector.
  - The comparator accepted comparator-VT.json in the d261c19 replay.
  - `∃ C` comes before `∀ E` in the proved type, and C is the scalar GD constant.
  - The transfer proof is sound. Integrability and continuity are correct. It is polymorphic over `Type u` and specialised to `Type`. The junk branch cannot occur.
  - No BLOCKER.
- **(b) is false in its strongest part.** The "C after E" plant implies the uniform-family theorem by a single instantiation, with no duality. I compiled the proof.
- **(c) The reading of the decay check is right; the diagnosis is wrong.** Q(3) has exact cusp points. The "folds only" classification is a grid-resolution artifact, so t^{-5/6} is never the asymptotic rate.
- **(d)** The records still state the false Q(3) classification as fact. The VT records lag.

## MAJOR

**M1. QWZ m = 3 is not "nondegenerate or fold everywhere": it has exact cusp points. The diagnosis in §5 is wrong.**
Files: `docs/design/vector-amplitudes.md:70-77` (§4) and `:84-96` (§5); `numerics/results-classify-vv-2026-11-08.txt` (Q(3) verdict NFD4).
- **The exact argument.** ω is symmetric under k₁↔k₂, so at any point (a, a): H₁₁ = H₂₂, T₁₁₁ = T₂₂₂ and T₁₁₂ = T₁₂₂.
  - Where H₁₁(a) = H₁₂(a), det H = 0 and ker H = span(1, −1).
  - T[v,v,v] = T₁₁₁ − 3T₁₁₂ + 3T₁₂₂ − T₂₂₂ = 0 identically there.
  - So `FoldOrNondegMatrix` fails at that point; the point is not a D4 point either.
- **Where the points are.** H₁₁ − H₁₂ changes sign on the diagonal at a = 1.910633 for m = 3. H₁₁ = H₁₂ = 5.09e−3 there, and |T| = 1.34.
  - Closed form: /tmp/advVT/qwz.py. Independent finite-difference check: /tmp/advVT/qwz_fd.py.
  - By evenness in each variable there are 4 points, (±a, ±a).
  - The same happens at m = 2.05, 4 and 8.
- **It is a genuine cusp.** Along the fold curve, |T[w,w,w]|/|T| vanishes linearly: 0.012, 0.036, 0.119, 0.330 at offsets 1e−4, 3e−4, 1e−3, 3e−3 (/tmp/advVT/qwz2.py). That is a Whitney cusp, generically A3, with local rate t^{-3/4}.
- **Why the classifier missed it.** Its grid spacing is 2π/2048 ≈ 3.1e−3. It reported minfold = 0.158 at (−1.910016, −1.911340), about 1e−3 from the cusp. Newton seeding only starts when f < 1e−2 (`classify_vv.rs:234`), so it never seeded there.
- **Consequences.**
  - "The classification … can be true while the constant is large; t^{-5/6} only at very large t" (§5) is false. The asymptotic rate is at best t^{-3/4}. t^{-2/3} is the near-umbilic regime that the computed times show.
  - GD-F, GD (with D = ∅) and GD-C (with K′ covering all the gradients needed for uniformity in x) do not apply to Q(m) for m > 2. So "a t^{-2/3} bound … needs the same classification" is moot: no proved theorem in the repository covers it.
  - Corroboration: the QWZ sups track the lattice-Laplacian control within 0.3% for t ≥ 23.
- **Was anything frozen?** Nothing frozen depends on this; the VT statements are generic. But the records state the classification as fact (see m5).
- **Fix.**
  - Record an erratum: Q(m), m > 2, has 4 cusp points (exact by the symmetry argument).
  - Retract the "folds with tiny margins" diagnosis.
  - Add symmetry-line or local-refinement checks to the classifier, or a positive control with a sub-grid cusp.
  - Drop QWZ m > 2 as a GD-F acceptance model.

**M2. The "C after E" plant is not rejected for a semantic reason. A reordered proof succeeds by one instantiation, without duality.**
Files: `docs/replay/2026-11-08-VT-sanity-plants.txt:14-16` ("a reordered proof cannot succeed either … without the duality argument"); `review/2026-11-08-VT-pre-proof-answers.md:11-13` ("cannot succeed by instantiation"); `OscInt/Front/VectorSanity.lean:91-93`.
- **Proof.** /tmp/advVT/plant_reorder.lean derives `P_globalNondeg_uniform_dim` from the verbatim run-2 planted statement.
  - It instantiates E = `lp (fun n => EuclideanSpace ℂ (Fin n)) ∞`.
  - Each ℂⁿ embeds by `lp.single` as a linear isometry, using `lp.norm_single` and `LinearIsometry.integral_comp_comm`.
  - No Hahn–Banach is used. Exit 0; axioms are propext, Classical.choice and Quot.sound.
- **What follows.** For a family indexed by a set, "C after E" gives one constant via a single big space. As both pre-proof referees said, the rejection only reflects how the proof script is written. The file also contradicts itself: lines 19-20 say this plant "is not detected and rests on the blind reviews".
- **Fix.** Retract the claim in all three places and keep the run-1 wording: brittleness only, and the two forms are equivalent. Optionally commit my derivation as an "accepted" control.

## MINOR

**m1. The FiniteDimensional plant is fixed only for GD-N-V.**
- The answers say B MINOR-1 is "Fixed", but only `globalNondeg_bounded` has an infinite-dimensional datum.
- `[FiniteDimensional ℂ E]` added to GD-F-V, GD-V and GD-C-V is accepted by their sanity theorems: /tmp/advVT/plant_findim_others.lean, exit 0.
- Fix: add `ℕ →ᵇ ℂ` data for those three, or narrow the record.

**m2. The plant generator counts any error as "rejected".**
- `plants_vt.py.txt` does not check that the first error sits at the mutation, or that a reordered proof fails.
- Run 2's semantic claim (M2) went beyond what the tool measures.
- Fix: label every verdict as specific to the proof shape.

**m3. Prereg criterion (b) cannot discriminate.**
- For t^{-2/3}, the max/min of t^{5/6}·sup over [8, 64] is 8^{1/6} = 1.41. For t^{-1/2} it is 2. Both are below 3. The observed 1.47 "PASS" means nothing.
- There is no positive control that does decay like t^{-5/6}, so the method was never shown able to see that rate on this window.
- `docs/prereg/2026-11-08-VV-qwz-decay.md:27`.

**m4. The route-order claim is narrow and not timestamped.**
- c24d0ea precedes d261c19 in the commit DAG, which is true.
- But the proof draft existed while the referee ran (`docs/proof-VT.md`, revision paragraph). The M1 fix adds `HasCompactSupport.intro` and `image_eq_zero_of_notMem_tsupport`, which the referee never named; they come from the draft.
- This is allowed by lessons 42. The claim should not be read as "route reviewed before the proof was written".

**m5. Records (d).**
- **Overclaims about QWZ:**
  - `CHANGELOG.md:23-25`: "QWZ band at m = 3 is nondegenerate-or-fold everywhere", stated as fact.
  - `docs/HANDOFF.md:40-43`: "nondegenerate or fold everywhere (so GD-F, rate t^{−5/6})"; VV "next" with that model.
  - `docs/ROADMAP.md:21-22`: "folds only".
  - None of these mention the failed decay check. All are false per M1.
- **VT is understated** (acceptable while the post-proof review is pending):
  - `stamps/statements.json` has 52 entries, but `docs/STATUS.md` has no VT rows.
  - HANDOFF says "48 pinned statements … each with a row in STATUS", which is no longer true at HEAD.
  - No CHANGELOG entry for VT.

## NIT

- **n1.** `OscInt/Front/VectorFinal.lean:101-111`: the docstrings say "any complex Banach space" without "(E : Type)". The statement docstrings and `docs/statements.md` §VT item 1 state the restriction correctly. `OscInt.VectorAux.transfer`, recommended for higher universes, sits in an Aux namespace outside the stable surface.
- **n2.** `OscInt/Front/VectorParts.lean:56`: `hM0` is unused (route N2 said so; it was kept).
- **n3. Instance diamond.** Inside the statements the only ℝ-structure is `NormedSpace.complexToReal`. Any two `NormedSpace ℝ` structures on a normed ℂ-space agree propositionally (ℚ-linearity plus continuity), so there is no semantic issue.
  - Default-transparency defeq holds for ℂ, ℂ×ℂ, `Fin 2 → Fin 2 → ℂ`, `ℕ →ᵇ ℂ` and EuclideanSpace (sanity file), and for `lp` (my file).
  - It is not syntactic: in my lp file, `rw` failed on both the `iteratedFDeriv` term and the integral, while `change` and `exact` worked. A one-line consumer note would help.
- **n4.** `docs/design/vector-amplitudes.md:21-23`: the §1 label "PLAUSIBLE … not yet used" is stale; it is now proved.
- **n5.** The stamps bound when statements and reviews existed, not when no proof existed. STATUS already says so; repeat it wherever claim (a) is quoted.

## Attacked and found sound
- **Integrability and continuity:** pointwise, through `notMem_tsupport_iff_eventuallyEq` and `ContinuousOn` on open U; `HasCompactSupport.intro`.
- **Junk value:** the Bochner-integral junk value cannot occur.
- **Edge cases:** M < 0 is vacuous, and E = 0 is handled.
- **Universe handling.**
- **Quantifier order:** proved type equals the frozen text, checked by the comparator and by TYPE-OK.
- **E = ℂ:** the specialisation is the scalar statement (`simpa [smul_eq_mul]`).
- **Plant outputs:** the run-2 outputs are consistent; all 7 ok-files are empty.
