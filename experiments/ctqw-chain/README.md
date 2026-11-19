<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->
# A quantum walk on a chain of qubits against a certified reference (registered, not run)

Protocol: `docs/prereg/2026-11-16-CTQW-chain.md`. Nothing here has been run on hardware; a hardware run needs the
owner's approval and account. The credentials are meant to live as secrets of the GitHub environment
`ibm-hardware`, so that every job that uses them waits for the owner's release (protocol, Addendum 2, item 10).

| File | What it is |
|---|---|
| `reference.py` → `reference.json` | certified enclosures (python-flint) of the exact and the Trotter-circuit populations and second moments |
| `circuits.py` | the registered circuits (Qiskit) |
| `simulate.py` → `simulation.json` | two more implementations that share no code with the reference (numpy state vector; Qiskit), and the noise simulation behind the tolerances |
| `tolerance.json` | the registered tolerances, copied from `simulation.json` |
| `analysis.py` | the registered analysis of raw counts (standard library only) |
| `hardware/check_access.py` | a read-only access check: authenticates, reads the plan and the device list, compiles the registered circuits locally and estimates device time; it submits nothing and prints no usage figure |
| `hardware/requirements-py312.txt` | the hash-pinned Python environment of the hardware scripts |
| `hardware/run_hardware.py` | the run script of Addenda 1 and 2: `rehearse` (local simulator, not data), `dryrun` (server-side dry run, no device executes, not data), `submit N [A]` (one repetition, one job; its refusals are listed at the top of the file), `collect N` (fetches a job; a failed job gives a failure record), `merge` (joins five result files for the registered analysis) |
| `hardware/rehearsal/` | output of `rehearse FakeFez` and of the registered analysis on it: a rehearsal of the pipeline on a simulator built from a calibration snapshot, **not data** |
| `hardware/records/submitted.json` | the submit records, one per attempt; empty until something is submitted |
| `hardware/SUBMIT-TRIGGER` | its last line is the instruction for `.github/workflows/ctqw-hardware.yml`; `none` until the owner says otherwise |

Versions used on 2026-11-16, as printed by the running interpreter: Python 3.13.18, python-flint 0.9.0 (FLINT 3.6.0),
numpy 2.5.5, qiskit 2.6.2, qiskit-aer 0.18.2.

```bash
python3 -I reference.py > reference.json                 # seconds
python3 simulate.py reference.json > simulation.json     # about three minutes
python3 analysis.py runs.json reference.json tolerance.json
```

To run on hardware (after approval): build `chain_circuit(M, t)` for M in (5, 9) and t in ("0.5", "1", "1.5", "2"),
transpile for the back end with a recorded seed, run 4000 shots five times, convert the counts with `site_order`,
write them as `{"bit_order": "site0-left", "runs": [...]}` with the metadata of the protocol's section 6, and run
`analysis.py`. No step may be changed after the first run.
