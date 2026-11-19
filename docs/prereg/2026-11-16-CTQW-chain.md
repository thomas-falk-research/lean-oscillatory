# Pre-registration: a quantum walk of one excitation on a chain of qubits, against a certified reference

Registered 2026-11-16 (session 13), before any hardware data exists; the registration is the commit that adds this
file, and the stamp that follows it bounds its time. Status: **REGISTERED, NOT RUN.** A run on real hardware needs
the owner's approval and account (given on 2026-11-16 for a no-cost plan of IBM Quantum: Addendum 1, written before
any run). After the first hardware run only the run log at the end of this file changes; any
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

## Addendum 1 (registered before any hardware run): the first run, on IBM Quantum

Added on 2026-11-16 after the owner approved a run on a no-cost plan of IBM Quantum with the owner's account. It
fixes what sections 2 and 6 left to "the device" and changes nothing else; the registered circuits, shots,
tolerances, analysis and decision rule stand. The commit that adds this addendum is stamped before the first job is
submitted; the stamp directory is named in the run log.

1. **Cost.** Only an instance on IBM's no-cost plan is used. The run script reads the plan of the instance and
   refuses to submit on any other plan. Every job carries a limit on its execution time.
2. **Device.** Among the operational, non-simulator devices of that instance with at least 9 qubits, the one with
   the fewest pending jobs at the moment of the first submission. All five repetitions run on that device. The
   list of candidates with their queue lengths at that moment is recorded.
3. **Qubits and compilation.** As registered: the device's transpiler at optimisation level 3 with seed 20261116
   chooses the qubits and compiles to the device's native gates; the layout and the two-qubit gate counts are
   recorded. If the native two-qubit gate is not `cz`, the counts of section 4 are compared with the counts of the
   device's own two-qubit gate.
4. **Primitive and options.** The Sampler primitive (version 2), 4000 shots per circuit, with dynamical decoupling,
   gate twirling and measurement twirling switched off explicitly, and no error mitigation of any kind.
5. **Repetitions.** Five jobs, each holding the eight circuits once (repetition r = 1, …, 5), submitted at least
   one hour apart if the plan's allowance and the queue permit, otherwise as the queue permits; the submission and
   completion times are recorded, and whether the device's calibration changed between repetitions is read from
   the calibration data recorded with each job.
6. **Failures.** A job that is rejected before it executes may be resubmitted unchanged and the rejection is
   recorded. A job that executed is never repeated: its counts are the data of that repetition, whatever they are.
   If the allowance ends before five repetitions exist, the run is INVALID by the registered rule and is reported
   as such with the data obtained.
7. **Dress rehearsal (not data).** Before the first job, the same script runs the same circuits on a simulator that
   uses a published calibration snapshot of an IBM device. Its result is reported as a rehearsal of the pipeline. It
   cannot change a tolerance or the decision rule.
8. **What is recorded** (section 6, made concrete): the device name and its reported version, the calibration
   data as returned by the service at each submission, the job identifiers, the SDK versions, the transpiler seed,
   the layout, the raw counts as returned, and the bit order used to convert them to "site 0 left-most". The
   instance identifier and any account detail are not recorded in the repository.

## Addendum 2 (registered before any hardware run): what Addendum 1 left open

Added on 2026-11-19, before any job has been sent to any device and before the commit that holds it is stamped; the
stamp directory is named in the run log. It follows a fresh-context review of the run script
(`experiments/ctqw-chain/hardware/run_hardware.py`) that found points which Addendum 1 would have left to chance or
to the lead's judgement at run time. It changes no circuit, no shot number, no tolerance, no analysis and no
decision rule. Everyone who wrote or checked it is an instance of one AI model family; no human has reviewed it.

1. **Device, ties.** If several devices share the fewest pending jobs at the first submission, the first in the
   alphabetical order of their names is used. (On 2026-11-19 three devices were visible, each with no pending job;
   a tie is the expected case.) "Operational" is the flag the service reports under that name; the status text is
   recorded and does not enter the rule.
2. **Qubits.** Each of the eight circuits is compiled on its own, at each submission, against the device as it
   then is; the circuits of one chain may therefore sit on different qubits at different times and in different
   repetitions. The qubit measured for each site and every qubit a circuit touches are recorded.
3. **Primitive.** "The Sampler primitive (version 2)" is `SamplerV2` as exported by the pinned client
   (qiskit-ibm-runtime 0.52.1), which sends a program to the service's executor; the class and the program
   identifier are recorded with each job.
4. **Limit per job.** 60 seconds of device time (the estimate is about 8 seconds per job). If the service refuses
   that value, the refusal is a rejection before execution.
5. **Spacing.** A repetition is not submitted less than one hour after the previous one; the script refuses.
6. **Failures (Addendum 1, item 6, made testable).** Every job carries the tags `ctqw-chain-2026-11-16` and
   `ctqw-chain-repN-aA` (repetition N, attempt A). Before a submission the script looks for a job with that tag, by
   the service's tag search and by reading the tags of the recent jobs, and refuses if one exists. A job that ends without results gets a failure record (status, the
   service's reason, time stamps, usage). It counts as **executed** if the service reports device usage above zero
   or a time stamp for the start of its run; it is then the datum of that repetition (INVALID by the registered
   rule, since it has no counts) and is not repeated. Otherwise it was **rejected before execution** and may be
   resubmitted unchanged as the next attempt; the classification is written into the submit record by the lead
   after the owner has seen the failure record, and before a resubmission the script itself asks the service
   for the state of the earlier attempt and refuses unless it ended without results and without usage. This rule
   rests on what the service reports; if its reports turn out not to distinguish the two cases, the job counts as
   executed.
7. **Record.** For every job: the counts as returned and the converted counts (site 0 left-most), the options
   actually set on the sampler, the calibration data of the touched qubits at submission and as recorded with the
   job, the candidates and their queue lengths at submission, the compiled two-qubit gate counts beside those of
   section 4. Not recorded anywhere in the repository, in a log or in an artifact: the key, any instance or account
   identifier, the instance's usage figures. (The access check of 2026-11-19, 14:09Z, printed the plan name and the
   allowance figures in a public log before this item existed.)
8. **Joining the five results.** `run_hardware.py merge` joins the five result files into the one file that the
   registered `analysis.py` reads; it changes no count.
9. **Dry run (not data).** Before the first submission one server-side dry run of the same eight circuits may be
   made: the service validates the job and returns mock results, and no device executes anything. It tests that
   the service accepts the job (the 60-second limit included), that the result can be decoded, and that the job
   is found again by its tag. It cannot change anything in this protocol.
10. **Approval.** The credentials are held as secrets of a GitHub environment with the owner as required
    reviewer; every job that uses them, including the read-only ones, waits for the owner's release. The lead
    writes an instruction into the trigger file only on the owner's explicit word for that instruction.

## Run log

No run yet.
