# 1. Scientific case

**Title.** A certified reference for quantum walks on a chain of qubits: machine-checked lattice dynamics, enclosed
numerically, tested against EuroHPC quantum hardware under a pre-registered protocol.

**Applicant.** `[APPLICANT-NAME]`, `[APPLICANT-AFFILIATION]`, `[APPLICANT-COUNTRY]` (`[APPLICANT-LEGAL-FORM]`).

## 1.1 The question

When a quantum processor simulates a single excitation hopping along a chain of qubits, what should it output, and
with what guaranteed accuracy is that reference known? Today the reference is a classical simulation, and published
experiments report agreement as an overlap between 0.90 and 0.98 with it (`docs/design/unlock-map.md`, section 6,
sources read on 2026-11-16). The reference itself is trusted, not certified.

This project supplies a reference that is certified at every link:
1. **A machine-checked theorem.** For the equation `i u′ + Δu = 0` on the lattice ℤ^d, every solution is the
   convolution of its initial datum with an explicit kernel, and `‖u(t)‖_∞ ≤ min{1, (C*/2π)^d (2|t|)^{−d/3}} ‖f‖₁`
   with `C* = 8(1 + √7)/3`. These are statements LS-K and LS-D of OscInt, proved in Lean 4 with Mathlib and
   replayed by six independent kernels (`docs/STATUS.md`, rows LS-K and LS-D; replay record
   `docs/replay/2026-11-14-session11-LS-final-verify-all.txt`). PROVEN (machine-checked); statement fidelity reviewed
   by AI referees, not yet by a human expert.
2. **A certified enclosure of the predicted numbers.** The site populations of a chain of 9 identical sites are
   enclosed by ball arithmetic, for example 0.33261 at the two neighbours of the starting site at time 1 (in units of
   the inverse hopping), with a radius below 2e-6 (`numerics/results-unlock-register-values-2026-11-16.txt`).
   VALIDATED (two methods that share no code agree: `numerics/results-unlock-chain-checks-2026-11-16.txt`, check K2).
3. **An exact account of the algorithmic error.** In the single-excitation sector the Trotter error of the circuit is
   computed exactly, not bounded: at most 0.00698 in any population for a second-order formula with step 1/4 (same
   record). VALIDATED.
4. **A protocol registered before any data exists** (prediction, tolerance, noise budget, analysis and decision rule;
   `docs/funding/02-work-plan.md`), time-stamped by several independent authorities as every OscInt statement is
   (`CONTRIBUTING.md`, step 4).

What remains after these four is the hardware error alone. The experiment measures it against a reference whose own
error is known and negligible.

## 1.2 Why it fits this call

The call is for users "who want to collect performance data or test a method on a target system". The method under
test is a benchmark with a certified reference: a family of circuits (a Trotterised exchange chain, one excitation)
whose ideal output is known to many digits for every chain length and time, with a proved envelope for the peak
population that holds for every time. Unlike random-circuit benchmarks, the output has physical structure (a ballistic
front, a known second moment) and is cheap to verify classically at any size.

## 1.3 What is new, and what is not

- **Not new:** the physics. The spreading of one excitation on a uniform chain follows squared Bessel functions; this
  has been observed in waveguide arrays since 2008 and on superconducting arrays since about 2021 (sources in
  `docs/design/unlock-map.md`, section 6). The decay rate `t^{−1/3}` is classical, and a smaller explicit constant
  than OscInt's is in print for lattice sites (`docs/prior_art.md`, disclosure of 2026-11-16).
- **New, as far as a logged search found** (PLAUSIBLE-not-novel, never PROVEN-novel): a hardware comparison in which
  the reference rests on a machine-checked theorem and certified numerics, and in which the protocol is registered
  before the run. The search found no machine-checked lattice dispersive estimate outside OscInt
  (`docs/prior_art.md`).
- **A stated gap.** The theorem is about the infinite lattice; a device is a finite chain. The link (a finite chain is
  the odd part of a ring, and a ring is the lattice summed over a sublattice) is proved on paper and validated by
  certified computation (checks K4 and K5), but is not yet machine-checked: ASSUMED(L4, the finite-chain statements
  are planned and not yet proved, project team). The predicted numbers do not depend on this gap, because they are
  computed for the finite chain directly.

## 1.4 Expected results

- Measured site populations and second moment of a 9-qubit chain at four times, with the registered comparison to
  the certified reference; a second, shorter chain as a control.
- A public data set and analysis that anyone can re-run, and a certified reference table that other users of the
  system can use as a benchmark without contacting the project.
- A negative result is a result: if the device does not meet the registered tolerance, the report says by how much
  and at which circuit depth.
