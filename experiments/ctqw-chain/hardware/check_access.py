#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Access check for the registered hardware run (docs/prereg/2026-11-16-CTQW-chain.md, Addendum 1).

It SUBMITS NOTHING: no job, no circuit and no session is sent to any device. It only
  1. authenticates to the service with the credentials in the environment,
  2. reads the plan of the active instance and whether its allowance covers the estimate (no figures are printed),
  3. lists the devices the registered rule would choose from, with their queue lengths,
  4. compiles the eight registered circuits locally for one candidate device (registered optimisation level and
     seed) and estimates the device time of the registered run from the device's own timing data.
The device named here is the candidate at the time of this check; the registered rule chooses the device at the
moment of the first submission, which is a later moment.

Output: one JSON object on standard output. It never contains the API key, an instance identifier, an account
identifier or an instance name; exception texts are printed with those values removed. With `--fake NAME` it runs
steps 3 and 4 against a simulated device of qiskit_ibm_runtime.fake_provider and needs no credentials (self-test).

Environment: QISKIT_IBM_TOKEN (an IBM Cloud API key); optionally QISKIT_IBM_INSTANCE (the instance's CRN).
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from circuits import CHAINS, TIMES, chain_circuit  # noqa: E402

SHOTS = 4000          # registered
REPETITIONS = 5       # registered
SEED = 20261116       # registered transpiler seed
OPT_LEVEL = 3         # registered
MIN_QUBITS = 9        # registered


def redact(text, secrets):
    for s in secrets:
        if s:
            text = text.replace(s, "<redacted>")
    return text


def describe_backend(backend):
    status = backend.status()
    return {"name": backend.name, "qubits": backend.num_qubits, "operational": bool(status.operational),
            "status": str(status.status_msg), "pending_jobs": int(status.pending_jobs)}


def estimate(backend):
    """Compile the registered circuits for `backend` (no submission) and estimate the device time."""
    from qiskit.transpiler import generate_preset_pass_manager
    pm = generate_preset_pass_manager(optimization_level=OPT_LEVEL, backend=backend, seed_transpiler=SEED)
    two_qubit = {name for name in backend.target.operation_names
                 if backend.target.operation_from_name(name).num_qubits == 2}
    rep_delay = None
    for getter in (lambda: backend.default_rep_delay, lambda: backend.configuration().default_rep_delay):
        try:
            rep_delay = float(getter())
            break
        except Exception:
            continue
    rows, per_repetition = [], 0.0
    for M in CHAINS:
        for t in TIMES:
            qc = pm.run(chain_circuit(M, t))
            ops = qc.count_ops()
            try:
                duration = float(qc.estimate_duration(backend.target, unit="s"))
            except Exception as exc:                      # timing data missing for some instruction
                duration = None
                note = type(exc).__name__
            else:
                note = ""
            row = {"sites": M, "time": t, "two_qubit_gates": int(sum(ops.get(g, 0) for g in two_qubit)),
                   "depth": int(qc.depth()), "duration_s": duration}
            if note:
                row["duration_note"] = note
            rows.append(row)
            if duration is not None and rep_delay is not None:
                per_repetition += SHOTS * (duration + rep_delay)
    complete = rep_delay is not None and all(r["duration_s"] is not None for r in rows)
    return {"candidate_device": backend.name, "two_qubit_gate_names": sorted(two_qubit),
            "default_rep_delay_s": rep_delay, "circuits": rows,
            "estimate_complete": complete,
            "estimated_device_seconds_per_repetition": per_repetition if complete else None,
            "estimated_device_seconds_registered_run": REPETITIONS * per_repetition if complete else None,
            "estimate_excludes": "per-job overhead added by the service; classical compilation; queue time"}


def main():
    out = {"script": "check_access.py", "submits_jobs": False, "registered": {
        "shots": SHOTS, "repetitions": REPETITIONS, "circuits": len(CHAINS) * len(TIMES),
        "transpiler_seed": SEED, "optimization_level": OPT_LEVEL}}
    import qiskit
    import qiskit_ibm_runtime
    out["versions"] = {"python": sys.version.split()[0], "qiskit": qiskit.__version__,
                       "qiskit_ibm_runtime": qiskit_ibm_runtime.__version__}
    if len(sys.argv) not in (1, 3) or (len(sys.argv) == 3 and sys.argv[1] != "--fake"):
        print("usage: check_access.py [--fake NAME]")
        return 2
    if len(sys.argv) == 3:
        import qiskit_ibm_runtime.fake_provider as fake
        backend = getattr(fake, sys.argv[2])()
        out["mode"] = "self-test on a simulated device; no credentials used"
        out["estimate"] = estimate(backend)
        print(json.dumps(out, indent=1))
        return 0
    token = os.environ.get("QISKIT_IBM_TOKEN", "")
    instance = os.environ.get("QISKIT_IBM_INSTANCE", "")
    secrets = [token, instance]
    out["mode"] = "live account, read-only"
    out["credentials_present"] = {"QISKIT_IBM_TOKEN": bool(token), "QISKIT_IBM_INSTANCE": bool(instance)}
    if not token:
        out["result"] = "NO TOKEN: the secret QISKIT_IBM_TOKEN is empty or not visible to this workflow"
        print(json.dumps(out, indent=1))
        return 1
    step = "authenticate"
    try:
        from qiskit_ibm_runtime import QiskitRuntimeService
        kwargs = {"channel": "ibm_quantum_platform", "token": token}
        if instance:
            kwargs["instance"] = instance
        service = QiskitRuntimeService(**kwargs)
        out["authenticated"] = True
        step = "instances"
        instances = list(service.instances())
        secrets += [str(i.get(k, "")) for i in instances for k in ("crn", "name")]
        out["instances_visible"] = len(instances)
        out["plans_visible"] = sorted({str(i.get("plan", "?")) for i in instances})
        active = service.active_instance()
        secrets.append(str(active or ""))
        plan = next((str(i.get("plan", "?")) for i in instances if i.get("crn") == active), None)
        out["active_instance_plan"] = plan
        step = "usage"
        usage = service.usage()
        out["usage_limit_reached"] = bool(usage.get("usage_limit_reached"))
        remaining = usage.get("usage_remaining_seconds")
        step = "devices"
        backends = service.backends(min_num_qubits=MIN_QUBITS)
        listed = [describe_backend(b) for b in backends]
        out["devices"] = sorted(listed, key=lambda d: (d["pending_jobs"], d["name"]))
        ok = [b for b, d in zip(backends, listed) if d["operational"] and not getattr(b, "simulator", False)]
        if not ok:
            out["result"] = "AUTHENTICATED, but no operational device with at least 9 qubits is visible"
            print(redact(json.dumps(out, indent=1), secrets))
            return 1
        step = "compile and estimate"
        candidate = min(ok, key=lambda b: (b.status().pending_jobs, b.name))
        out["estimate"] = estimate(candidate)
        need = out["estimate"]["estimated_device_seconds_registered_run"]
        out["allowance_at_least_three_times_the_estimate"] = (
            bool(remaining >= 3 * need) if isinstance(remaining, (int, float)) and need else None)
        out["result"] = "OK: authenticated; nothing was submitted"
    except Exception as exc:
        out["result"] = f"FAILED at step '{step}': {type(exc).__name__}"
        out["error_text"] = redact(str(exc), secrets)[:600]
        print(redact(json.dumps(out, indent=1), secrets))
        return 1
    print(redact(json.dumps(out, indent=1), secrets))
    return 0


if __name__ == "__main__":
    sys.exit(main())
