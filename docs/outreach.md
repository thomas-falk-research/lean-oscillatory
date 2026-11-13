# Adoption and outreach: prepared for the owner (nothing here has been submitted)

Every item below is a draft. The owner decides whether, when and where to submit it. Facts in the drafts point at
evidence in this repository; re-check `docs/STATUS.md` before posting, since statuses can change.

## 1. Reservoir listing
Reservoir (the Lean package index) lists packages from GitHub that build with Lake and carry a licence; an
inclusion step is on the Reservoir side (see its documentation at the time of submission; not checked from this
session). What OscInt already has: `lakefile.toml` with `name = "oscint"` and a `version`, an Apache-2.0 `LICENSE`,
tagged releases (`v0.2.0` to `v0.4.0`; `v0.5.0` prepared), a README section on depending on the package, and `examples/consumer-release/`
built against the tag in CI. Owner steps: follow Reservoir's current submission procedure; add the badge to README
once listed.

## 2. Lean Zulip announcement (draft, channel `#announce` or `#mathlib4 > analysis`)
> **OscInt: machine-checked uniform oscillatory-integral estimates in Lean 4 + Mathlib**
>
> OscInt (github.com/thomas-falk-research/lean-oscillatory, Apache-2.0, Lean v4.35.0, Mathlib v4.35.0) proves
> uniform estimates for oscillatory integrals: van der Corput for every derivative order with explicit constants,
> non-stationary and nondegenerate stationary phase, the uniform fold bound m^{-5/6}, the uniform cusp (A3) bound
> t^{-3/4}, the uniform D4 (umbilic) bound t^{-2/3} with its exact leading term Γ(1/3)²/(√3 |Disc|^{1/6}), and global
> decay from a pointwise classification of the phase — every point nondegenerate, a fold, or one of finitely many D4
> points gives m^{-2/3} uniformly over all linear terms. For lattices: the 1D kernel
> ∫_{−π}^{π} e^{i(t cos k + ξk)} dk is bounded by 8(1 + √7)/3 · t^{-1/3} for every t > 0 and real ξ (within a
> factor 2 of the best constant), and the kernel on ℤ^d by (8(1 + √7)/3)^d t^{-d/3}; in 2D the rate t^{-2/3} is sharp.
>
> Every theorem's statement was frozen (RFC 3161 timestamps) and reviewed blind before its proof was written
> (exceptions are disclosed in `docs/STATUS.md`);
> proofs replay in several kernels; `stamps/statements.json` and `tools/oscint_check.py` let a downstream project
> check in CI that it depends on exactly the reviewed statements. Entry point `import OscInt.API`; decision tree
> `docs/which-theorem.md`; machine-readable index `docs/api.json`.
>
> Reviews so far are by AI referees; a human expert reading the statements (`docs/statements.md` against
> `OscInt/Statements/`) would be very welcome.

## 3. Mathlib upstream PRs (first three, per the downstream request)
From `docs/upstream.md`, in this order:
1. `exists_smooth_partition_compact` (finite C^∞ partition of unity with compact supports, finite-dimensional normed
   space) → `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` (normed-space corollary). Work: port to `module` syntax,
   generalise the index set, docstring, a test.
2. `integral_polar` → `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean` (Mathlib has a polar change of variables, `integral_comp_polarCoord_symm`, name to be `#check`ed before the PR;
   the new lemma is the iterated form with θ outer for functions vanishing outside a radius).
3. The uniform Leibniz bound `norm_iteratedFDeriv_mul_le_of_forall_le` (2ⁿ B M) →
   `Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`.
Each needs: a Mathlib fork branch, `module`/`public import` conversion, Mathlib naming review, `lake exe lint-style`,
and a PR description. No PR is opened without the owner's go (`docs/upstream.md`).

## 4. Preprint outline (8–12 pages; venue the owner's choice: ITP, CPP, or a journal's software track)
1. Problem: uniform oscillatory-integral estimates are the analytic core of dispersive estimates, caustics and
   stationary-phase approximations; their hypotheses are subtle (uniformity, degenerate critical points).
2. What is verified: the statement list (S1–S5, front ends, global decay, lattice kernels with explicit constants),
   each with its frozen text and status; what is not (dimension ≥ 3 beyond separable lattice kernels, global assembly
   with cusps, leading terms of nondegenerate stationary phase, the lattice Schrödinger group of batch LS).
3. How: statement-first protocol (frozen `Prop`, timestamps, blind pre-proof review, sanity theorems through the
   statement constants with planted controls), proof campaigns with parallel agents on blueprint interfaces, the
   trust chain (axiom audit, statement-type check, comparator, multi-kernel replay, commitments), and the downstream
   checker. Numbers: statements, lines, review verdicts, replay times.
4. What it enables: the 2D lattice-Laplacian dispersive estimate as a worked example; the decision tree; the API index
   evaluated by an agent.
5. Lessons: the failures the process caught (`docs/lessons.md`: a kernel accepting an ill-typed theorem under a
   metaprogram, a vacuous Gamma-free check, a referee proving what it reviewed, records that did not exist).
6. Limitations and AI-use statement: proofs and reviews largely by AI agents; no human review of the statements yet.
