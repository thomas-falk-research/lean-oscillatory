#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Run script of the registered hardware experiment (docs/prereg/2026-11-16-CTQW-chain.md, Addendum 1).

  rehearse FAKE_NAME      Addendum 1, item 7. The registered circuits, compiled as registered, sampled on a local
                          simulator built from the calibration snapshot of an IBM device
                          (qiskit_ibm_runtime.fake_provider). Needs no credentials and contacts nobody. NOT DATA.
  submit R                Submit repetition R (1 to 5): ONE Sampler job holding the eight registered circuits once,
                          4000 shots each. It does not wait for the job. Refuses unless the environment variable
                          CTQW_OWNER_APPROVAL equals "submit repetition R" (set only by the gated workflow), unless
                          the instance is on the no-cost plan, and unless the earlier repetitions are on record.
  collect R               Fetch the finished job of repetition R and write its raw counts in the registered format.
                          Submits nothing.

Records (JSON, one object on standard output; `submit` and `collect` also write the file named by --out):
  submit  -> {"repetition", "device", "job_id", "submitted_utc", "candidates", "circuits": [layout, gate counts],
              "calibration", "options", "versions"}
  collect -> {"bit_order": "site0-left", "runs": [...]} as experiments/ctqw-chain/analysis.py reads it, each run
             with "meta" (job, device, times, usage).
No key, instance identifier, instance name or account identifier is written; exception texts are redacted.

State between repetitions is the file --record (default: records/submitted.json beside this script): the list of
the submit records so far, committed to the repository after each submission. Repetition 1 chooses the device by
the registered rule; repetitions 2 to 5 use the device on record.

Environment for `submit` and `collect`: QISKIT_IBM_TOKEN, optionally QISKIT_IBM_INSTANCE.
"""
import argparse
import datetime
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
from circuits import CHAINS, TIMES, chain_circuit, site_order  # noqa: E402

SHOTS = 4000                 # registered
REPETITIONS = 5              # registered
SEED = 20261116              # registered transpiler seed
OPT_LEVEL = 3                # registered
MIN_QUBITS = 9               # Addendum 1, item 2
NO_COST_PLAN = "open"        # Addendum 1, item 1
MAX_EXECUTION_TIME = 120     # seconds per job (Addendum 1, item 1: every job carries a limit)
REHEARSAL_SEEDS = [17, 1017, 2017, 3017, 4017]


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def redact(text, secrets):
    for s in secrets:
        if s:
            text = text.replace(s, "<redacted>")
    return text


def versions():
    import qiskit
    import qiskit_ibm_runtime
    out = {"python": sys.version.split()[0], "qiskit": qiskit.__version__,
           "qiskit_ibm_runtime": qiskit_ibm_runtime.__version__}
    try:
        import qiskit_aer
        out["qiskit_aer"] = qiskit_aer.__version__
    except Exception:
        pass
    return out


def compile_all(backend):
    """The eight registered circuits, compiled as registered. Returns [(M, t, circuit, record)]."""
    from qiskit.transpiler import generate_preset_pass_manager
    pm = generate_preset_pass_manager(optimization_level=OPT_LEVEL, backend=backend, seed_transpiler=SEED)
    two_qubit = {name for name in backend.target.operation_names
                 if backend.target.operation_from_name(name).num_qubits == 2}
    out = []
    for M in CHAINS:
        for t in TIMES:
            qc = pm.run(chain_circuit(M, t))
            ops = qc.count_ops()
            physical = [int(q) for q in qc.layout.final_index_layout(filter_ancillas=True)]
            rec = {"sites": M, "time": t, "physical_qubits_by_site": physical,
                   "two_qubit_gates": int(sum(ops.get(g, 0) for g in two_qubit)),
                   "two_qubit_gate_names": sorted(two_qubit), "depth": int(qc.depth())}
            out.append((M, t, qc, rec))
    return out


def calibration(backend, qubits):
    """Calibration data of the qubits used, as published by the back end now (section 6 of the protocol)."""
    out = {"backend_version": str(getattr(backend, "backend_version", "") or ""), "qubits": {}}
    try:
        props = backend.properties()
    except Exception as exc:
        out["note"] = f"properties unavailable: {type(exc).__name__}"
        return out
    if props is None:
        out["note"] = "properties unavailable"
        return out
    out["last_update_utc"] = str(getattr(props, "last_update_date", ""))
    for q in sorted(set(qubits)):
        row = {}
        for key, fn in (("t1_s", lambda: props.t1(q)), ("t2_s", lambda: props.t2(q)),
                        ("readout_error", lambda: props.readout_error(q)),
                        ("sx_error", lambda: props.gate_error("sx", q))):
            try:
                row[key] = float(fn())
            except Exception:
                row[key] = None
        out["qubits"][str(q)] = row
    pairs = {}
    two_qubit = [name for name in backend.target.operation_names
                 if backend.target.operation_from_name(name).num_qubits == 2]
    used = set(qubits)
    for name in two_qubit:
        for pair in backend.target[name]:
            if pair is not None and set(pair) <= used:
                try:
                    pairs[f"{name}:{pair[0]}-{pair[1]}"] = float(props.gate_error(name, list(pair)))
                except Exception:
                    pairs[f"{name}:{pair[0]}-{pair[1]}"] = None
    out["two_qubit_errors"] = pairs
    return out


def sampler_for(mode, simulator_seed=None):
    from qiskit_ibm_runtime import SamplerV2
    sampler = SamplerV2(mode=mode)
    sampler.options.default_shots = SHOTS
    sampler.options.dynamical_decoupling.enable = False       # Addendum 1, item 4
    sampler.options.twirling.enable_gates = False
    sampler.options.twirling.enable_measure = False
    if simulator_seed is None:
        sampler.options.max_execution_time = MAX_EXECUTION_TIME
    else:
        sampler.options.simulator.seed_simulator = simulator_seed
    return sampler


OPTIONS_RECORD = {"primitive": "SamplerV2", "shots": SHOTS, "dynamical_decoupling": False, "twirling_gates": False,
                  "twirling_measure": False, "error_mitigation": "none",
                  "max_execution_time_s": MAX_EXECUTION_TIME, "transpiler_seed": SEED,
                  "optimization_level": OPT_LEVEL}


def counts_site0_left(pub_result, M):
    raw = pub_result.join_data().get_counts()
    out = {}
    for bits, n in raw.items():
        key = site_order(bits.replace(" ", ""))
        if len(key) != M:
            raise ValueError(f"bit string of length {len(key)} for a chain of {M} sites")
        out[key] = out.get(key, 0) + int(n)
    if sum(out.values()) != SHOTS:
        raise ValueError(f"{sum(out.values())} shots returned, {SHOTS} registered")
    return out


def rehearse(fake_name):
    import qiskit_ibm_runtime.fake_provider as fake
    backend = getattr(fake, fake_name)()
    compiled = compile_all(backend)
    runs = []
    for r, seed in enumerate(REHEARSAL_SEEDS, start=1):
        job = sampler_for(backend, simulator_seed=seed).run([qc for _, _, qc, _ in compiled])
        result = job.result()
        for i, (M, t, _, rec) in enumerate(compiled):
            runs.append({"sites": M, "time": t, "repetition": r, "shots": SHOTS,
                         "counts": counts_site0_left(result[i], M),
                         "meta": {"rehearsal": True, "simulated_device": backend.name, "simulator_seed": seed,
                                  "circuit": rec}})
    used = [q for _, _, _, rec in compiled for q in rec["physical_qubits_by_site"]]
    return {"bit_order": "site0-left", "not_data": "REHEARSAL on a simulator; not a hardware result",
            "versions": versions(), "options": OPTIONS_RECORD, "calibration_snapshot": calibration(backend, used),
            "runs": runs}


def connect():
    token = os.environ.get("QISKIT_IBM_TOKEN", "")
    instance = os.environ.get("QISKIT_IBM_INSTANCE", "")
    if not token:
        raise SystemExit("NO TOKEN: QISKIT_IBM_TOKEN is empty or not visible")
    from qiskit_ibm_runtime import QiskitRuntimeService
    kwargs = {"channel": "ibm_quantum_platform", "token": token}
    if instance:
        kwargs["instance"] = instance
    service = QiskitRuntimeService(**kwargs)
    instances = list(service.instances())
    active = service.active_instance()
    secrets = [token, instance, str(active or "")] + [str(i.get(k, "")) for i in instances for k in ("crn", "name")]
    plan = next((str(i.get("plan", "")) for i in instances if i.get("crn") == active), "")
    return service, plan, secrets


def load_record(path):
    if not os.path.exists(path):
        return []
    with open(path) as fh:
        data = json.load(fh)
    return data["submissions"]


def submit(rep, record_path, out_path):
    approval = os.environ.get("CTQW_OWNER_APPROVAL", "")
    if approval != f"submit repetition {rep}":
        raise SystemExit(f"REFUSED: CTQW_OWNER_APPROVAL is not 'submit repetition {rep}'; nothing was submitted")
    earlier = load_record(record_path)
    done = sorted(int(s["repetition"]) for s in earlier)
    if done != list(range(1, rep)):
        raise SystemExit(f"REFUSED: repetitions on record are {done}; repetition {rep} is not the next one")
    service, plan, secrets = connect()
    try:
        if plan != NO_COST_PLAN:
            raise SystemExit("REFUSED: the active instance is not on the no-cost plan; nothing was submitted")
        usage = service.usage()
        if usage.get("usage_limit_reached"):
            raise SystemExit("REFUSED: the usage limit of the instance is reached; nothing was submitted")
        backends = service.backends(min_num_qubits=MIN_QUBITS)
        candidates = []
        for b in backends:
            st = b.status()
            candidates.append({"name": b.name, "qubits": b.num_qubits, "operational": bool(st.operational),
                               "status": str(st.status_msg), "pending_jobs": int(st.pending_jobs),
                               "simulator": bool(getattr(b, "simulator", False))})
        if rep == 1:
            ok = [c for c in candidates if c["operational"] and not c["simulator"]]
            if not ok:
                raise SystemExit("REFUSED: no operational device with at least 9 qubits; nothing was submitted")
            device = min(ok, key=lambda c: (c["pending_jobs"], c["name"]))["name"]
        else:
            device = earlier[0]["device"]
        backend = service.backend(device)
        compiled = compile_all(backend)
        used = [q for _, _, _, rec in compiled for q in rec["physical_qubits_by_site"]]
        calib = calibration(backend, used)
        sampler = sampler_for(backend)
        job = sampler.run([qc for _, _, qc, _ in compiled])
        rec = {"repetition": rep, "device": device, "job_id": job.job_id(), "submitted_utc": now(),
               "candidates_at_submission": sorted(candidates, key=lambda c: (c["pending_jobs"], c["name"])),
               "usage_before": {k: v for k, v in usage.items() if isinstance(v, (int, float, bool))},
               "circuits": [r for _, _, _, r in compiled], "calibration": calib,
               "options": OPTIONS_RECORD, "versions": versions()}
    except SystemExit:
        raise
    except Exception as exc:
        raise SystemExit(redact(f"FAILED: {type(exc).__name__}: {exc}", secrets)[:600])
    text = redact(json.dumps(rec, indent=1, sort_keys=True), secrets)
    if out_path:
        with open(out_path, "w") as fh:
            fh.write(text + "\n")
    return text


def collect(rep, record_path, out_path):
    earlier = load_record(record_path)
    mine = [s for s in earlier if int(s["repetition"]) == rep]
    if len(mine) != 1:
        raise SystemExit(f"REFUSED: no single submission on record for repetition {rep}")
    sub = mine[0]
    service, _, secrets = connect()
    try:
        job = service.job(sub["job_id"])
        status = str(job.status())
        if not job.in_final_state():
            raise SystemExit(f"NOT FINISHED: the job of repetition {rep} has status {status}; nothing was fetched")
        if not job.done():
            raise SystemExit(f"JOB DID NOT COMPLETE: status {status}; this is recorded, not repeated "
                             "(Addendum 1, item 6, says when a resubmission is allowed)")
        result = job.result()
        metrics = job.metrics()
        meta = {"job_id": sub["job_id"], "device": sub["device"], "submitted_utc": sub["submitted_utc"],
                "collected_utc": now(), "status": status,
                "timestamps": metrics.get("timestamps"), "usage": metrics.get("usage"),
                "options": sub["options"], "versions_at_submission": sub["versions"],
                "versions_at_collection": versions(), "calibration_at_submission": sub["calibration"]}
        runs = []
        order = [(M, t) for M in CHAINS for t in TIMES]
        for i, (M, t) in enumerate(order):
            circ = next(c for c in sub["circuits"] if c["sites"] == M and c["time"] == t)
            runs.append({"sites": M, "time": t, "repetition": rep, "shots": SHOTS,
                         "counts": counts_site0_left(result[i], M), "meta": dict(meta, circuit=circ)})
    except SystemExit:
        raise
    except Exception as exc:
        raise SystemExit(redact(f"FAILED: {type(exc).__name__}: {exc}", secrets)[:600])
    text = redact(json.dumps({"bit_order": "site0-left", "runs": runs}, indent=1, sort_keys=True), secrets)
    if out_path:
        with open(out_path, "w") as fh:
            fh.write(text + "\n")
    return text


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("rehearse")
    a.add_argument("fake_name")
    for name in ("submit", "collect"):
        a = sub.add_parser(name)
        a.add_argument("repetition", type=int, choices=range(1, REPETITIONS + 1))
        a.add_argument("--record", default=os.path.join(HERE, "records", "submitted.json"))
        a.add_argument("--out", default="")
    args = ap.parse_args()
    if args.cmd == "rehearse":
        text = json.dumps(rehearse(args.fake_name), indent=1, sort_keys=True)
    elif args.cmd == "submit":
        text = submit(args.repetition, args.record, args.out)
    else:
        text = collect(args.repetition, args.record, args.out)
    print(text)
    print("sha256 of the record text above: " + hashlib.sha256((text + "\n").encode()).hexdigest(), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
