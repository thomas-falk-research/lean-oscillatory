# Pre-registration: a quantum walk of one excitation on a chain of qubits, against a certified reference

Registered 2026-11-16 (session 13), before any hardware data exists; the registration is the commit that adds this
file, and the stamp that follows it bounds its time. Status: **REGISTERED, NOT RUN.** A run on real hardware needs
the owner's approval and account. After the first hardware run only the run log at the end of this file changes; any
other change is a deviation and is recorded as one.

## 1. What is tested, and what is not

- **Tested:** that a gate-based quantum processor, running the registered circuit, reproduces the site populations
  of one excitation on an open chain of M identical sites to within a registered tolerance. The reference is
  certified: the populations of the registered Trotter circuit are enclosed by ball arithmetic, and they are within
  a certified distance of the exact dynamics.
- **The machine-checked statement behind the reference:** LS-K of OscInt (every solution of the lattice Schrödinger
  equation is the kernel convolution of its datum; `docs/STATUS.md`). It is a statement about the infinite lattice.
  The finite chain is linked to it by reflection and periodisation, on paper and by certified computation
  (`numerics/results-unlock-chain-checks-2026-11-16.txt`, checks K4 and K5), not yet by a machine-checked theorem:
  ASSUMED(L4, the finite-chain statements are not proved, lead). The registered numbers are computed for the finite
  chain directly and do not depend on that link.
- **Not tested:** any OscInt bound. The envelope `p_max(t) ≤ min{1, (C*/2π)²(2t)^{−2/3}}` of LS-D equals 1 for
  `t ≤ 1.85` and is 0.950 at `t = 2`, far above every population here. It is reported and cannot fail on a working
  device. No new physics is expected: this is a device benchmark with a certified reference.

## 2. System and circuit

- Chains of M = 5 and M = 9 qubits in a line; one excitation prepared on the centre qubit (site index M // 2).
- Dynamics: the exchange coupling `(XX + YY)/2` on each bond, hopping 1; in the one-excitation sector
  `i u′ = −(u_{a+1} + u_{a−1})` with missing neighbours at the ends.
- Circuit: second-order Trotter formula with step 1/4; bond layers alternate between even and odd bonds
  (`experiments/ctqw-chain/circuits.py`). Times t = 1/2, 1, 3/2, 2: 5, 9, 13, 17 bond layers.
- Measurement: all qubits, computational basis, 4000 shots per circuit. Five repetitions of every circuit, on
  different calibration cycles of the device where the access allows it.
- Compilation: to the device's native gates by its own transpiler at its highest optimisation level, with a fixed
  seed that is recorded. On a line with the basis {cz, rz, sx, x} the reference transpilation gives the two-qubit
  gate counts of section 4.

## 3. Reference values (certified)

`experiments/ctqw-chain/reference.py` (python-flint, 200 bits) writes `experiments/ctqw-chain/reference.json`: for
each chain and time, enclosures of the exact populations, of the Trotter-circuit populations, of both second moments,
and of the total-variation distance between the two distributions. The largest such distance is 0.00876 (9 sites,
t = 1); the registered comparison is with the Trotter-circuit populations, so the algorithmic error does not enter.

Independent implementations (`experiments/ctqw-chain/simulate.py`, record
`experiments/ctqw-chain/simulation.json`): a numpy state-vector simulation of the full 2^M-dimensional space with
gate matrices built from Pauli matrices, and Qiskit's exact state vector of the registered circuits. Their
populations differ from the certified reference by at most 2.4e-15 and 4.5e-16. VALIDATED (three implementations
that share no code).

## 4. Noise budget and power analysis (simulation only)

Noise model (Qiskit Aer): a depolarising error after every two-qubit gate (p2) and every `sx` or `x` gate (p1), and a
symmetric readout error (r). Three levels: ideal (0, 0, 0); **nominal (p2 = 3e-3, p1 = 3e-4, r = 1.5e-2)**, chosen
inside the range of the public calibration list of one vendor on 2026-11-16 (`docs/design/unlock-map.md`, section 6);
poor (1e-2, 1e-3, 3e-2). For each circuit and level, 30 seeds of 4000 shots were sampled and analysed by the
registered analysis. The tolerance of each circuit is the nominal mean distance plus three standard deviations,
rounded up to three decimals. The model has no coherent errors, no crosstalk and no leakage: ASSUMED(L1, a
simulated noise model, lead); a real device can differ in either direction.

| Sites | Time | Two-qubit gates | Depth | Tolerance (TVD) | Ideal: mean TVD; runs above tolerance | Nominal: mean TVD; kept fraction; runs above | Poor: mean TVD; kept fraction; runs above |
|---|---|---|---|---|---|---|---|
| 5 | 0.5 | 20 | 42 | 0.025 | 0.0099; 0/30 | 0.0113; 0.886; 0/30 | 0.0197; 0.744; 5/30 |
| 5 | 1 | 36 | 69 | 0.030 | 0.0108; 0/30 | 0.0148; 0.853; 0/30 | 0.0380; 0.669; 26/30 |
| 5 | 1.5 | 52 | 97 | 0.034 | 0.0105; 0/30 | 0.0180; 0.822; 0/30 | 0.0649; 0.598; 30/30 |
| 5 | 2 | 68 | 125 | 0.039 | 0.0103; 0/30 | 0.0224; 0.792; 0/30 | 0.0828; 0.537; 30/30 |
| 9 | 0.5 | 40 | 42 | 0.032 | 0.0099; 0/30 | 0.0130; 0.790; 0/30 | 0.0316; 0.556; 11/30 |
| 9 | 1 | 72 | 69 | 0.042 | 0.0120; 0/30 | 0.0204; 0.730; 0/30 | 0.0592; 0.440; 29/30 |
| 9 | 1.5 | 104 | 97 | 0.042 | 0.0147; 0/30 | 0.0238; 0.675; 0/30 | 0.0632; 0.356; 29/30 |
| 9 | 2 | 136 | 125 | 0.049 | 0.0167; 0/30 | 0.0303; 0.629; 0/30 | 0.0890; 0.288; 30/30 |

Reading, with exact (Clopper–Pearson) 95% intervals for a proportion out of 30:
- **False alarms.** At the nominal level no run of 30 exceeded its tolerance, for every circuit: the per-run rate is
  in [0, 0.116].
- **Power.** At the poor level, for t ≥ 1 between 26 and 30 of 30 runs exceed the tolerance: a per-run detection rate
  of at least 0.69 (26/30: [0.693, 0.962]; 29/30: [0.828, 0.999]; 30/30: [0.884, 1]). At t = 1/2 the test has little
  power (5/30 and 11/30): the circuit is too shallow to separate the two noise levels, and those two rows are
  registered as controls of the pipeline, not as tests.
- **Shot-noise floor.** With no noise at all the distance is about 0.010 to 0.017 at 4000 shots, so a tolerance below
  about 0.02 would reject a perfect device.
- **Can the device resolve the prediction?** The populations differ between sites by 0.1 to 0.4; a distance of 0.03
  to 0.05 resolves the profile. The difference between the chain and the infinite line (largest population
  difference 0.030 at 9 sites, t = 2) is at the edge of the tolerance and is not a registered test.

## 5. Analysis and decision rule (fixed)

`experiments/ctqw-chain/analysis.py`, standard library only, on the raw counts:
1. Keep the shots with exactly one excitation. A run with fewer than 500 kept shots is INVALID.
2. Compute the kept fraction, the post-selected site distribution, its total-variation distance to the certified
   Trotter reference, and the second moment about the centre.
3. Per chain and time: **CONSISTENT** if the distance is at most the tolerance of section 4 in at least 4 of the 5
   repetitions; **NOT CONSISTENT** otherwise; INVALID if any run is invalid or the repetitions are not five.
4. Primary outcomes: the six decisions for t ≥ 1. Controls: the two decisions at t = 1/2.
5. Reported without a decision: kept fractions, second moments against their references, the LS-D envelope, the
   device's calibration snapshot.
No readout-error mitigation, no zero-noise extrapolation and no change of tolerance after the first run. If the
transpiled two-qubit gate count on the device differs from section 4 by more than 10%, the run is still analysed as
registered and the difference is reported.

## 6. Run record requirements

For every job: back-end name and version, date and time, calibration data as published by the back end at run time
(qubit list, T1, T2, gate and readout errors), SDK versions as printed by the running interpreter, transpiler seed,
job identifiers, and the raw counts with the bit order "site 0 left-most". Raw data is never edited.

## 7. Evidence labels

- The reference values: VALIDATED at rung L2 (certified enclosures; three implementations agree).
- The machine-checked statement: PROVEN at L4 for the infinite lattice (fidelity reviewed by AI referees, not yet by
  a human expert); the bridge to the finite chain is ASSUMED at L4, validated at L2.
- The tolerances and the power analysis: VALIDATED on a simulated noise model only (L1); 30 seeds per cell;
  seeds 17, 1017, …, 29017 of the Aer simulator and transpiler seed 20261116.
- Everyone who wrote or checked this protocol is an instance of one AI model family; no human has reviewed it.

## 8. The strongest case against this experiment

It cannot surprise. The physics is textbook and has been measured on other platforms for years; a pass shows that the
device is as good as the assumed noise level, a fail shows that it is not, and neither tests a theorem. The
tolerance is tied to a simulated noise model that the lead chose. What the experiment does give is a public,
certified reference for a family of circuits, an exactly computed algorithmic error, and one end-to-end exercise of
the chain from a frozen statement to raw data.

## Run log

No run yet.
