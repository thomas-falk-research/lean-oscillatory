#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Simulation of the registered experiment by implementations that share no code with reference.py, and the power
analysis that fixes the tolerances (docs/prereg/2026-11-16-CTQW-chain.md, sections 3 and 4).

S1  numpy only: the full 2^M state vector with explicit 4x4 gate matrices built from Pauli matrices; populations
    of the one-excitation basis states against the certified Trotter reference.
S2  Qiskit: the registered circuits of circuits.py, exact state vector (qiskit.quantum_info); same comparison.
S3  Qiskit Aer with a noise model (depolarising error after every two-qubit and one-qubit basis gate, symmetric
    readout error), circuits transpiled to the basis {cz, rz, sx, x} on a line; the registered analysis is run on
    the sampled counts. For each noise level: kept fraction and the distribution of the total-variation distance
    over SEEDS seeds. The tolerance is fixed from the level "nominal" as mean + 3 standard deviations, rounded up
    to 3 decimals, and the same statistic at the levels "ideal" and "poor" shows what the test can distinguish.
Usage: python3 simulate.py reference.json > simulation.json   (numpy, qiskit, qiskit-aer; versions recorded)
"""
import json
import math
import platform
import sys
from fractions import Fraction as F

import numpy as np
import qiskit
import qiskit_aer
from qiskit import transpile
from qiskit.quantum_info import Statevector
from qiskit.transpiler import CouplingMap
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel, ReadoutError, depolarizing_error

import analysis
import circuits

REF = json.load(open(sys.argv[1]))
SHOTS = 4000
SEEDS = 30
LEVELS = {"ideal": (0.0, 0.0, 0.0), "nominal": (3e-3, 3e-4, 1.5e-2), "poor": (1e-2, 1e-3, 3e-2)}  # p2, p1, readout
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)


def ref_mid(e):
    return float((F(e["lo"]) + F(e["hi"])) / 2)


def numpy_populations(M, time):
    """S1: site a is tensor factor a (left-most = site 0)."""
    H2 = (np.kron(X, X) + np.kron(Y, Y)) / 2
    w, V = np.linalg.eigh(H2)

    def gate(theta):
        return (V * np.exp(1j * theta * w)) @ V.conj().T

    def apply(psi, U, a):
        psi = psi.reshape([2] * M)
        psi = np.moveaxis(psi, [a, a + 1], [0, 1]).reshape(4, -1)
        psi = (U @ psi).reshape([2, 2] + [2] * (M - 2))
        return np.moveaxis(psi, [0, 1], [a, a + 1]).reshape(-1)

    def layer(psi, theta, parity):
        U = gate(theta)
        for a in range(parity, M - 1, 2):
            psi = apply(psi, U, a)
        return psi

    n = int(round(float(time) / circuits.DT))
    psi = np.zeros(2**M, dtype=complex)
    psi[1 << (M - 1 - M // 2)] = 1
    psi = layer(psi, circuits.DT / 2, 0)
    for s in range(n):
        psi = layer(psi, circuits.DT, 1)
        psi = layer(psi, circuits.DT if s < n - 1 else circuits.DT / 2, 0)
    return [abs(psi[1 << (M - 1 - a)]) ** 2 for a in range(M)], float(np.sum(np.abs(psi) ** 2))


def qiskit_populations(M, time):
    sv = Statevector(circuits.chain_circuit(M, time, measure=False))
    probs = sv.probabilities_dict()
    return [probs.get(circuits.site_order("".join("1" if b == a else "0" for b in range(M))), 0.0) for a in range(M)]


def noise_model(p2, p1, ro):
    nm = NoiseModel()
    if p2:
        nm.add_all_qubit_quantum_error(depolarizing_error(p2, 2), ["cz"])
    if p1:
        nm.add_all_qubit_quantum_error(depolarizing_error(p1, 1), ["sx", "x"])
    if ro:
        nm.add_all_qubit_readout_error(ReadoutError([[1 - ro, ro], [ro, 1 - ro]]))
    return nm


out = {"format": "oscint-ctqw-simulation/1", "shots": SHOTS, "seeds": SEEDS, "levels": LEVELS, "agreement": [],
       "two_qubit_gates": {}, "noise": {}, "tolerance": {},
       "versions": {"python": platform.python_version(), "numpy": np.__version__, "qiskit": qiskit.__version__,
                    "qiskit-aer": qiskit_aer.__version__}}
worst1 = worst2 = 0.0
for M in circuits.CHAINS:
    for ts in circuits.TIMES:
        ref = [ref_mid(e) for e in REF["chains"][str(M)]["times"][ts]["trotter"]]
        p1, norm = numpy_populations(M, ts)
        p2 = qiskit_populations(M, ts)
        d1 = max(abs(a - b) for a, b in zip(p1, ref))
        d2 = max(abs(a - b) for a, b in zip(p2, ref))
        worst1, worst2 = max(worst1, d1), max(worst2, d2)
        out["agreement"].append({"sites": M, "time": ts, "numpy_max_abs_diff": d1, "qiskit_max_abs_diff": d2,
                                 "numpy_one_excitation_weight": sum(p1), "numpy_norm": norm})
out["agreement_summary"] = {"numpy_worst": worst1, "qiskit_worst": worst2, "pass": bool(worst1 < 1e-12 and worst2 < 1e-12)}

for M in circuits.CHAINS:
    out["two_qubit_gates"][str(M)] = {}
    out["noise"][str(M)] = {}
    out["tolerance"][str(M)] = {}
    for ts in circuits.TIMES:
        qc = circuits.chain_circuit(M, ts)
        tqc = transpile(qc, basis_gates=["cz", "rz", "sx", "x"], coupling_map=CouplingMap.from_line(M),
                        optimization_level=3, seed_transpiler=20261116)
        ops = tqc.count_ops()
        out["two_qubit_gates"][str(M)][ts] = {"cz": int(ops.get("cz", 0)), "depth": int(tqc.depth()),
                                              "sx_x": int(ops.get("sx", 0) + ops.get("x", 0))}
        res = {}
        for level, (p2, p1, ro) in LEVELS.items():
            sim = AerSimulator(noise_model=noise_model(p2, p1, ro))
            tv, kept = [], []
            for seed in range(SEEDS):
                counts = sim.run(tqc, shots=SHOTS, seed_simulator=1000 * seed + 17).result().get_counts()
                run = {"runs": [{"sites": M, "time": ts, "repetition": seed, "shots": SHOTS,
                                 "counts": {circuits.site_order(k): int(v) for k, v in counts.items()}}]}
                row = analysis.analyse(run, REF, {str(M): {ts: 1.0}})["runs"][0]
                kept.append(row["kept_fraction"])
                tv.append(row.get("tvd", float("nan")))
            res[level] = {"tvd_mean": float(np.mean(tv)), "tvd_sd": float(np.std(tv, ddof=1)), "tvd_max": float(np.max(tv)),
                          "tvd_min": float(np.min(tv)), "kept_mean": float(np.mean(kept)), "kept_min": float(np.min(kept)),
                          "tvd": [float(x) for x in tv]}
        tol = math.ceil(1000 * (res["nominal"]["tvd_mean"] + 3 * res["nominal"]["tvd_sd"])) / 1000
        for level in LEVELS:
            res[level]["seeds_above_tolerance"] = int(sum(1 for x in res[level]["tvd"] if x > tol))
        out["noise"][str(M)][ts] = res
        out["tolerance"][str(M)][ts] = tol
print(json.dumps(out, indent=1))
