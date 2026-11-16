# 3. Resources requested, with justification

## 3.1 Quantum Access Pilot: `[TARGET-SYSTEM]`

**Request: the minimum allocation for the system (1 QPU hour for Euro-Q-Exa by the call's table, read once from an
image: re-read before submitting), for 3 months.**

| Item | Circuits | Shots each | Shots |
|---|---|---|---|
| registered runs: 2 chains × 4 times × 5 repetitions | 40 | 4000 | 160,000 |
| readout calibration, 2 chains × 5 repetitions × 2 basis states per qubit set | 20 | 4000 | 80,000 |
| pilot and qubit selection (WP 1) | 30 | 2000 | 60,000 |
| reserve for a repeated day and the registered fallback | 25 | 4000 | 100,000 |
| **total** | **115** | | **400,000** |

At a shot rate of `[CALIBRATION-DATA]` shots per second the QPU time is 400,000 divided by that rate. The rate was not
found in this session. With 1 millisecond per shot (ASSUMED, a typical order for superconducting systems, not a
figure for this system) the total is about 400 seconds of execution, which is 11% of one hour; queueing, compilation
and calibration overheads are charged differently on different systems, which is why the request is the minimum
allocation and not less. If the system's accounting makes one hour insufficient, the registered runs are cut to 3
repetitions before anything else.

Why not more: the experiment is a benchmark of fixed size, and nothing in the plan scales with more hours. Why this
system: a superconducting processor with nearest-neighbour coupling contains a 9-qubit path; the star-topology and
all-to-all systems of the pilot can run the same circuit but test a less native case, and the analogue systems cannot
run it as specified.

Classical resources: none requested. The reference computations take seconds on a laptop
(`numerics/review/unlock_register_values.py`).

## 3.2 Development Access: not recommended at this cut-off

The same cut-off offers 400 to 4,500 node-hours on EuroHPC supercomputers for code and algorithm development. The
honest assessment is that OscInt cannot justify such a request today:

| Workload | Size | Basis |
|---|---|---|
| a full six-kernel replay of the library | about 12 core-hours (3 hours on 4 cores) | `docs/replay/2026-11-15-session12-D4U-verify-all.txt` |
| a weekly replay for a year | about 620 core-hours, a few node-hours on a 128-core node | arithmetic from the row above |
| building Mathlib from source on a second machine | of the order of 100 core-hours (ASSUMED; not measured here) | `docs/ROADMAP.md`, section 6 |
| the registered census of dispersion relations | not yet implemented; size unknown | `docs/prereg/2026-11-09-CENSUS-prereg.md` |

These add up to well under 100 node-hours, and none of it is an HPC scaling problem, which is what the call's
assessment looks at ("a detailed description of the challenges hindering the scalability of the code"). A request
would be justified once there is a large certified computation to run, for example a branch-and-bound proof of a sharp
constant over a parameter domain. That work is not planned in detail yet (`docs/design/unlock-map.md`, section 7,
rank 9). Recommendation: do not apply to Development Access on 1 December; revisit when such a computation is
specified. Benchmark Access (200 to 3,500 node-hours for 3 months) is the lighter entry point then.
