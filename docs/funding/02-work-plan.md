# 2. Work plan

Duration: 3 months (the shorter of the two allocation periods the call offers). Target system: `[TARGET-SYSTEM]`
(the drafts assume the superconducting system Euro-Q-Exa; its device data, `[CALIBRATION-DATA]`, has not been read and
must be filled in before the circuit counts below are final).

## 2.1 The experiment

- **System simulated.** A chain of M = 9 qubits with nearest-neighbour exchange coupling, one excitation prepared at
  the centre qubit; the single-excitation sector obeys `i u′ = −(u_{a+1} + u_{a−1})` with missing neighbours at the
  ends. A second chain of M = 5 is the control.
- **Circuit.** A second-order Trotter formula with step 1/4 in units of the inverse hopping: alternating layers of
  two-qubit exchange rotations on even and odd bonds. Evolution times t = 1/2, 1, 3/2, 2 need 5, 9, 13 and 17 bond
  layers (9 and 17 are computed in `numerics/results-unlock-register-values-2026-11-16.txt`; 5 and 13 follow from the
  same formula, 2n + 1 layers for n steps).
- **Measured.** All qubits in the computational basis; shots with exactly one excitation are kept (the dynamics
  conserves the excitation number, so every other outcome is a detected error); the kept fraction is itself reported.
- **Quantities.** The population of each site; the second moment about the starting site; the kept fraction.
- **Reference.** Certified enclosures of the exact populations of the finite chain and of the Trotterised circuit, so
  the algorithmic error is separated exactly from the hardware error.

## 2.2 Work packages

| WP | When | Content | Output |
|---|---|---|---|
| 0 | before access | protocol registered and time-stamped: predictions with enclosures, tolerance, noise budget, analysis script, decision rule; simulation of the full pipeline by two implementations that share no code, with a noise model | a registration in `docs/prereg/` and its ledger line; a ready-to-run package |
| 1 | weeks 1–3 | device characterisation on the chosen qubits: readout assignment matrix, single- and two-qubit error from the system's own calibration data, a two-qubit pilot of the exchange rotation | calibration record; go or no-go on the qubit selection, by a rule fixed in WP 0 |
| 2 | weeks 3–8 | the registered runs: 2 chain lengths × 4 times × 5 repetitions on different days, 4000 shots each, plus readout-calibration circuits | raw counts with back-end metadata |
| 3 | weeks 8–10 | analysis exactly as registered; no change of metric or threshold after the first run | analysis record; deviations, if any, listed |
| 4 | weeks 10–12 | final report to EuroHPC; public release of raw data, code and the reference table | report; data deposit with a DOI |

## 2.3 Decision rule (to be fixed in the registration, sketched here)

For each chain and time, the total-variation distance between the measured post-selected distribution and the
certified reference is compared with a tolerance computed in WP 0 from the device's published error rates and the shot
noise. "Consistent with the reference" requires the distance to be within the tolerance in at least 4 of the 5
repetitions. The registered envelope `p_max(t) ≤ min{1, (C*/2π)² (2t)^{−2/3}}` is reported, but it is not a test:
at these times it is far above any clean device's peak (`docs/design/unlock-map.md`, section 6), and the registration
says so.

## 2.4 Team and effort

`[TEAM]`. The method, the reference computations and the analysis code exist or are in preparation in the public
repository; the hosting site's support is needed only for onboarding and for the device's calibration data.

## 2.5 What can stop the plan

- The target system cannot run a 17-layer circuit on 9 qubits with a usable kept fraction. Then the registered
  fallback is the 5-qubit chain at times up to 1, which needs 9 layers.
- The native gate set makes the exchange rotation cost more than two two-qubit gates. Then the step is enlarged under
  the registered rule, at a known and exactly computed Trotter error (0.0704 for a first-order formula at step 1/4 on
  9 sites, from the record above).
