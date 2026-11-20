#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""The registered circuits (Qiskit). One excitation at the centre of a chain of M qubits; second-order Trotter
steps of the exchange coupling with step DT; measurement of all qubits.

A bond layer applies exp(i theta (XX + YY)/2) on each bond of one parity; in the single-excitation sector this is
[[cos theta, i sin theta], [i sin theta, cos theta]]. Qiskit's XXPlusYYGate(phi) is exp(-i (phi/2) (XX + YY)/2), so
phi = -2 theta. Site a is qubit a; counts are converted to "site 0 left-most" bit strings by `site_order`.
"""
from qiskit import QuantumCircuit
from qiskit.circuit.library import XXPlusYYGate

DT = 0.25
CHAINS = [5, 9]
TIMES = ["0.5", "1", "1.5", "2"]


def bond_layer(qc, M, theta, parity):
    for a in range(parity, M - 1, 2):
        qc.append(XXPlusYYGate(-2 * theta, 0), [a, a + 1])


def chain_circuit(M, time, measure=True):
    n = int(round(float(time) / DT))
    qc = QuantumCircuit(M, M) if measure else QuantumCircuit(M)
    qc.x(M // 2)
    bond_layer(qc, M, DT / 2, 0)
    for s in range(n):
        bond_layer(qc, M, DT, 1)
        bond_layer(qc, M, DT if s < n - 1 else DT / 2, 0)
    if measure:
        qc.measure(range(M), range(M))
    return qc


def site_order(bitstring):
    """Qiskit prints classical bit 0 right-most; the analysis wants site 0 left-most."""
    return bitstring[::-1]
