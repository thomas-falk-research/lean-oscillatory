#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Run script of the registered hardware experiment (docs/prereg/2026-11-16-CTQW-chain.md, Addenda 1 and 2).

  rehearse FAKE_NAME   The registered circuits, compiled as registered, sampled on a local simulator built from the
                       calibration snapshot of an IBM device. No credentials, no network. NOT DATA.
  dryrun               One server-side dry run of the eight circuits (Addendum 2, item 9): the service validates
                       the job and returns mock results; NO DEVICE EXECUTES ANYTHING. Tests the remote path. NOT DATA.
  submit R [A]         Submit attempt A (default 1) of repetition R (1 to 5): ONE job holding the eight registered
                       circuits once, 4000 shots each. Does not wait for the device.
  collect R            Fetch the job of the latest attempt of repetition R. A finished job gives the raw counts; a
                       failed or cancelled job gives a failure record. Submits nothing.
  merge FILE...        Join the five result files into the one file the registered analysis reads; compare the
                       compiled two-qubit gate counts with section 4. No credentials, no network.

`submit` refuses: without the guard variable (CTQW_GUARD="submit repetition R attempt A": a guard against accident,
not a proof of approval; the approval is the owner's release of the workflow job that holds the credentials);
without an explicit instance; on any plan but the no-cost one; if the usage limit is reached; if the earlier
repetitions are not on record; if this repetition already has an attempt that is not marked as rejected before
execution; if less than an hour has passed since the previous repetition was submitted; and if the service already
holds a job with this attempt's tag (in which case it prints that job's identifier, so a lost one is recovered).

Everything is printed on standard output; nothing meaningful goes to standard error. Records are built from named
fields only and never contain the key, an instance identifier, an instance name, an account identifier or the
instance's usage figures. Texts of exceptions are printed redacted and cut to 300 characters.

State between runs: --record (default records/submitted.json beside this script), a list of the submit records,
committed to the repository by the lead after each submission. Repetition 1 chooses the device by the registered
rule; later repetitions use the device on record.

Environment for dryrun, submit, collect: QISKIT_IBM_TOKEN and QISKIT_IBM_INSTANCE (both required).
"""
import argparse
import datetime
import hashlib
import json
import os
import sys
import urllib.parse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
from circuits import CHAINS, TIMES, chain_circuit, site_order  # noqa: E402

SHOTS = 4000                 # registered
REPETITIONS = 5              # registered
SEED = 20261116              # registered transpiler seed
OPT_LEVEL = 3                # registered
MIN_QUBITS = 9               # Addendum 1, item 2
NO_COST_PLAN = "open"        # Addendum 1, item 1
MAX_EXECUTION_TIME = 60      # seconds of device time per job (Addendum 2, item 4)
MIN_SPACING_S = 3600         # Addendum 1, item 5
FAMILY_TAG = "ctqw-chain-2026-11-16"
REHEARSAL_SEEDS = [17, 1017, 2017, 3017, 4017]
ORDER = [(M, t) for M in CHAINS for t in TIMES]
SECTION4_TWO_QUBIT = {(5, "0.5"): 20, (5, "1"): 36, (5, "1.5"): 52, (5, "2"): 68,
                      (9, "0.5"): 40, (9, "1"): 72, (9, "1.5"): 104, (9, "2"): 136}
RETURNED_ORDER = "classical bit 0 right-most (Qiskit); reversed by circuits.site_order to site 0 left-most"


class Refused(Exception):
    """A deliberate refusal or a stop with a message that is safe to print."""


def utcnow():
    return datetime.datetime.now(datetime.timezone.utc)


def stamp(dt=None):
    return (dt or utcnow()).strftime("%Y-%m-%dT%H:%M:%SZ")


def secret_forms(token, instance, extra=()):
    """Every form of the credentials that must never be printed: whole, percent-encoded, and the parts of a CRN."""
    forms = set()
    for s in (token, instance, *extra):
        if not s:
            continue
        forms.add(s)
        forms.add(urllib.parse.quote(s, safe=""))
        forms.add(urllib.parse.quote(s))
    generic = {"bluemix", "public", "quantum-computing", "crn", "v1"}
    for part in instance.replace("/", ":").split(":") if instance else ():
        if len(part) >= 8 and part not in generic and not part.startswith(("us-", "eu-", "jp-", "au-")):
            forms.add(part)
    return sorted((f for f in forms if f), key=len, reverse=True)


def redact(text, forms):
    for s in forms:
        text = text.replace(s, "<redacted>")
    return text


def safe_error(exc, forms):
    return f"FAILED: {type(exc).__name__}: " + redact(str(exc), forms)[:300]


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


def two_qubit_names(backend):
    return sorted(name for name in backend.target.operation_names
                  if backend.target.operation_from_name(name).num_qubits == 2)


def compile_all(backend):
    """The eight registered circuits, each compiled on its own as registered. Returns [(M, t, circuit, record)]."""
    from qiskit.transpiler import generate_preset_pass_manager
    pm = generate_preset_pass_manager(optimization_level=OPT_LEVEL, backend=backend, seed_transpiler=SEED)
    two_qubit = set(two_qubit_names(backend))
    out = []
    for M, t in ORDER:
        qc = pm.run(chain_circuit(M, t))
        ops = qc.count_ops()
        measured = [int(q) for q in qc.layout.final_index_layout(filter_ancillas=True)]
        active = sorted({int(qc.find_bit(q).index) for inst in qc.data for q in inst.qubits})
        n2 = int(sum(ops.get(g, 0) for g in two_qubit))
        ref = SECTION4_TWO_QUBIT[(M, t)]
        rec = {"sites": M, "time": t, "measured_physical_qubit_by_site": measured, "active_physical_qubits": active,
               "two_qubit_gates": n2, "two_qubit_gates_section4": ref,
               "within_10_percent_of_section4": bool(abs(n2 - ref) * 10 <= ref),
               "two_qubit_gate_names": sorted(two_qubit), "depth": int(qc.depth()),
               "operations": {str(k): int(v) for k, v in sorted(ops.items())}}
        out.append((M, t, qc, rec))
    return out


def calibration(backend, qubits, props=None, source="back end at this moment"):
    """Calibration data of the given physical qubits (section 6 of the protocol)."""
    out = {"source": source, "backend_version": str(getattr(backend, "backend_version", "") or ""), "qubits": {}}
    if props is None:
        try:
            props = backend.properties()
        except Exception as exc:
            out["note"] = f"properties unavailable: {type(exc).__name__}"
            return out
    if props is None:
        out["note"] = "properties unavailable"
        return out
    upd = getattr(props, "last_update_date", None)
    try:
        out["last_update_utc"] = stamp(upd.astimezone(datetime.timezone.utc))
    except Exception:
        out["last_update_as_given"] = str(upd)
    used = sorted(set(int(q) for q in qubits))
    for q in used:
        row = {}
        for key, fn in (("t1_s", lambda: props.t1(q)), ("t2_s", lambda: props.t2(q)),
                        ("readout_error", lambda: props.readout_error(q)),
                        ("sx_error", lambda: props.gate_error("sx", q)),
                        ("x_error", lambda: props.gate_error("x", q))):
            try:
                row[key] = float(fn())
            except Exception:
                row[key] = None
        out["qubits"][str(q)] = row
    pairs = {}
    for name in two_qubit_names(backend):
        for pair in backend.target[name]:
            if pair is not None and set(pair) <= set(used):
                try:
                    pairs[f"{name}:{pair[0]}-{pair[1]}"] = float(props.gate_error(name, list(pair)))
                except Exception:
                    pairs[f"{name}:{pair[0]}-{pair[1]}"] = None
    out["two_qubit_errors"] = pairs
    return out


def make_sampler(mode, tags=None, simulator_seed=None):
    from qiskit_ibm_runtime import SamplerV2
    sampler = SamplerV2(mode=mode)
    sampler.options.default_shots = SHOTS
    sampler.options.dynamical_decoupling.enable = False       # Addendum 1, item 4
    sampler.options.twirling.enable_gates = False
    sampler.options.twirling.enable_measure = False
    if simulator_seed is None:
        sampler.options.max_execution_time = MAX_EXECUTION_TIME
        sampler.options.environment.job_tags = list(tags or [])
    else:
        sampler.options.simulator.seed_simulator = simulator_seed
    return sampler


def options_record(sampler, remote):
    o = sampler.options
    return {"sampler_class": type(sampler).__module__ + "." + type(sampler).__qualname__,
            "default_shots": o.default_shots,
            "dynamical_decoupling_enable": o.dynamical_decoupling.enable,
            "twirling_enable_gates": o.twirling.enable_gates,
            "twirling_enable_measure": o.twirling.enable_measure,
            "error_mitigation": "none (a sampler has none; nothing is applied to the counts)",
            "max_execution_time_s": o.max_execution_time if remote else None,
            "job_tags": list(o.environment.job_tags or []) if remote else None,
            "transpiler_seed": SEED, "optimization_level": OPT_LEVEL}


def counts_of(pub_result, M):
    """(counts as returned, counts with site 0 left-most) for one circuit."""
    raw = {str(k): int(v) for k, v in pub_result.join_data().get_counts().items()}
    out = {}
    for bits, n in raw.items():
        key = site_order(bits.replace(" ", ""))
        if len(key) != M or set(key) - {"0", "1"}:
            raise Refused(f"FAILED: a returned bit string does not fit a chain of {M} sites")
        out[key] = out.get(key, 0) + n
    if sum(out.values()) != SHOTS:
        raise Refused(f"FAILED: {sum(out.values())} shots returned for one circuit, {SHOTS} registered")
    return raw, out


def rehearse(fake_name):
    import qiskit_ibm_runtime.fake_provider as fake
    backend = getattr(fake, fake_name)()
    compiled = compile_all(backend)
    runs = []
    options = None
    for r, seed in enumerate(REHEARSAL_SEEDS, start=1):
        sampler = make_sampler(backend, simulator_seed=seed)
        options = options_record(sampler, remote=False)
        result = sampler.run([qc for _, _, qc, _ in compiled]).result()
        for i, (M, t, _, rec) in enumerate(compiled):
            raw, conv = counts_of(result[i], M)
            runs.append({"sites": M, "time": t, "repetition": r, "shots": SHOTS, "counts": conv,
                         "counts_as_returned": raw,
                         "meta": {"rehearsal": True, "simulated_device": backend.name, "simulator_seed": seed,
                                  "circuit": rec}})
    used = [q for _, _, _, rec in compiled for q in rec["active_physical_qubits"]]
    return {"bit_order": "site0-left", "returned_bit_order": RETURNED_ORDER,
            "not_data": "REHEARSAL on a local simulator; not a hardware result",
            "versions": versions(), "options": options,
            "calibration_snapshot": calibration(backend, used, source="calibration snapshot of the simulated device"),
            "runs": runs}


def connect():
    """Returns (service, secret forms). Requires both credentials; checks the plan of the one instance in use."""
    token = os.environ.get("QISKIT_IBM_TOKEN", "")
    instance = os.environ.get("QISKIT_IBM_INSTANCE", "")
    if not token or not instance:
        raise Refused("REFUSED: QISKIT_IBM_TOKEN and QISKIT_IBM_INSTANCE must both be visible; nothing was done")
    forms = secret_forms(token, instance)
    try:
        from qiskit_ibm_runtime import QiskitRuntimeService
        service = QiskitRuntimeService(channel="ibm_quantum_platform", token=token, instance=instance)
        instances = list(service.instances())
        forms = secret_forms(token, instance, [str(i[k]) for i in instances for k in ("crn",) if i.get(k)])
        if service.active_instance() != instance:
            raise Refused("REFUSED: the active instance is not the one given; nothing was done")
        plans = [str(i.get("plan", "")) for i in instances if i.get("crn") == instance]
        if plans != [NO_COST_PLAN]:
            raise Refused("REFUSED: the instance is not on the no-cost plan; nothing was done")
        if service.usage().get("usage_limit_reached"):
            raise Refused("REFUSED: the usage limit of the instance is reached; nothing was done")
    except Refused:
        raise
    except Exception as exc:
        raise Refused(safe_error(exc, forms))
    return service, forms


def load_record(path):
    with open(path) as fh:
        data = json.load(fh)
    subs = data["submissions"]
    ids = [s["job_id"] for s in subs]
    if len(ids) != len(set(ids)):
        raise Refused("REFUSED: the record holds one job identifier twice")
    devices = {s["device"] for s in subs}
    if len(devices) > 1:
        raise Refused("REFUSED: the record names more than one device")
    return subs


def candidates_now(service):
    out = []
    for b in service.backends(min_num_qubits=MIN_QUBITS):
        st = b.status()
        out.append({"name": b.name, "qubits": int(b.num_qubits), "operational": bool(st.operational),
                    "status": str(st.status_msg), "pending_jobs": int(st.pending_jobs),
                    "simulator": bool(getattr(b, "simulator", False))})
    return sorted(out, key=lambda c: (c["pending_jobs"], c["name"]))


def choose_device(candidates):
    """Addendum 1, item 2, with the tie-break of Addendum 2, item 1 (alphabetical order of the device names)."""
    ok = [c for c in candidates if c["operational"] and not c["simulator"]]
    if not ok:
        raise Refused("REFUSED: no operational device with at least 9 qubits; nothing was submitted")
    best = min(c["pending_jobs"] for c in ok)
    tied = sorted(c["name"] for c in ok if c["pending_jobs"] == best)
    return tied[0], tied


def tag_of(rep, attempt):
    return f"ctqw-chain-rep{rep}-a{attempt}"


def describe_job(job):
    try:
        status = str(job.status())
    except Exception as exc:
        status = f"unknown ({type(exc).__name__})"
    return f"job_id={job.job_id()} status={status}"


def submit(rep, attempt, record_path, out_path):
    tag = tag_of(rep, attempt)
    if os.environ.get("CTQW_GUARD", "") != f"submit repetition {rep} attempt {attempt}":
        raise Refused(f"REFUSED: CTQW_GUARD is not 'submit repetition {rep} attempt {attempt}'; nothing was submitted")
    subs = load_record(record_path)
    by_rep = {}
    for s in subs:
        by_rep.setdefault(int(s["repetition"]), []).append(s)
    if sorted(r for r in by_rep if r < rep) != list(range(1, rep)) or any(r > rep for r in by_rep):
        raise Refused(f"REFUSED: repetitions on record are {sorted(by_rep)}; repetition {rep} is not the next one")
    mine = sorted(by_rep.get(rep, []), key=lambda s: int(s["attempt"]))
    if [int(s["attempt"]) for s in mine] != list(range(1, attempt)):
        raise Refused(f"REFUSED: attempts on record for repetition {rep} are "
                      f"{[int(s['attempt']) for s in mine]}; attempt {attempt} is not the next one")
    if any(s.get("outcome") != "rejected-before-execution" for s in mine):
        raise Refused(f"REFUSED: repetition {rep} has an attempt that is not marked as rejected before execution; "
                      "a job that executed is never repeated (Addendum 1, item 6)")
    spacing = None
    earlier = [s for s in subs if int(s["repetition"]) < rep and s.get("outcome") != "rejected-before-execution"]
    if earlier:
        last = max(datetime.datetime.strptime(s["submitted_utc"], "%Y-%m-%dT%H:%M:%SZ")
                   .replace(tzinfo=datetime.timezone.utc) for s in earlier)
        spacing = int((utcnow() - last).total_seconds())
        if spacing < MIN_SPACING_S:
            raise Refused(f"REFUSED: {spacing} s since the previous repetition was submitted; "
                          f"{MIN_SPACING_S} s are registered; nothing was submitted")
    service, forms = connect()
    job = None
    rec = {"repetition": rep, "attempt": attempt, "job_tags": [FAMILY_TAG, tag]}
    try:
        existing = list(service.jobs(job_tags=[tag], limit=5))
        if existing:
            raise Refused("REFUSED: the service already holds a job with the tag of this attempt: "
                          + "; ".join(describe_job(j) for j in existing) + ". Nothing was submitted.")
        candidates = candidates_now(service)
        if subs:
            device, tied = subs[0]["device"], None
        else:
            device, tied = choose_device(candidates)
        backend = service.backend(device)
        compiled = compile_all(backend)
        used = [q for _, _, _, r in compiled for q in r["active_physical_qubits"]]
        sampler = make_sampler(backend, tags=[FAMILY_TAG, tag])
        rec.update({"device": device, "device_tied_candidates": tied,
                    "seconds_since_previous_repetition": spacing, "candidates_at_submission": candidates,
                    "circuits": [r for _, _, _, r in compiled],
                    "calibration_at_submission": calibration(backend, used),
                    "options_sent": options_record(sampler, remote=True), "versions": versions()})
        circuits = [qc for _, _, qc, _ in compiled]
        # ---- the one line that creates a job ----
        job = sampler.run(circuits)
        rec["job_id"] = job.job_id()
        rec["submitted_utc"] = stamp()
        print(f"JOB CREATED repetition {rep} attempt {attempt} job_id={rec['job_id']} device={device}", flush=True)
        try:
            rec["program_id"] = str(job.primitive_id)
        except Exception:
            rec["program_id"] = None
    except Refused:
        if job is None:
            raise
    except Exception as exc:
        if job is None:
            raise Refused(safe_error(exc, forms) + " | no job was created by this run as far as the client knows; "
                          "before any new attempt, `submit` asks the service for a job with this tag")
        rec["note_after_creation"] = safe_error(exc, forms)
    return finish(rec, forms, out_path)


def dryrun(out_path):
    if os.environ.get("CTQW_GUARD", "") != "dry run":
        raise Refused("REFUSED: CTQW_GUARD is not 'dry run'; nothing was sent")
    service, forms = connect()
    rec = {"not_data": "SERVER-SIDE DRY RUN: validated by the service, mock results, no device executed anything",
           "job_tags": [FAMILY_TAG, "ctqw-chain-dryrun"]}
    try:
        candidates = candidates_now(service)
        device, tied = choose_device(candidates)
        backend = service.backend(device)
        compiled = compile_all(backend)
        sampler = make_sampler(backend, tags=rec["job_tags"])
        rec.update({"device_used_for_validation": device, "device_tied_candidates": tied,
                    "circuits": [r for _, _, _, r in compiled],
                    "options_sent": options_record(sampler, remote=True), "versions": versions()})
        job = sampler.run([qc for _, _, qc, _ in compiled], dry_run=True)
        rec["job_id"] = job.job_id()
        rec["submitted_utc"] = stamp()
        print(f"DRY RUN CREATED job_id={rec['job_id']} device={device}", flush=True)
        try:
            rec["usage_estimation"] = job.usage_estimation
        except Exception as exc:
            rec["usage_estimation"] = f"unavailable: {type(exc).__name__}"
        result = job.result(timeout=600)
        shapes = []
        for i, (M, t) in enumerate(ORDER):
            raw, conv = counts_of(result[i], M)
            shapes.append({"sites": M, "time": t, "distinct_bit_strings": len(conv), "shots": sum(conv.values())})
        rec["decoded"] = shapes
        rec["result_count"] = len(result)
        rec["status"] = str(job.status())
        metrics = job.metrics()
        rec["usage"] = metrics.get("usage")
        rec["timestamps"] = metrics.get("timestamps")
    except Refused:
        raise
    except Exception as exc:
        rec["failed"] = safe_error(exc, forms)
    return finish(rec, forms, out_path)


def collect(rep, record_path, out_path):
    subs = load_record(record_path)
    mine = sorted((s for s in subs if int(s["repetition"]) == rep), key=lambda s: int(s["attempt"]))
    if not mine:
        raise Refused(f"REFUSED: no submission on record for repetition {rep}")
    sub = mine[-1]
    tag = tag_of(rep, int(sub["attempt"]))
    service, forms = connect()
    try:
        job = service.job(sub["job_id"])
        tags = list(job.tags or [])
        device = job.backend().name
        if tag not in tags or device != sub["device"]:
            raise Refused(f"REFUSED: the job on record does not carry the tag {tag} on device {sub['device']}")
        status = str(job.status())
        if not job.in_final_state():
            raise Refused(f"NOT FINISHED: the job of repetition {rep} has status {status}; nothing was fetched")
        metrics = job.metrics()
        meta = {"job_id": sub["job_id"], "job_tags": tags, "device": device, "attempt": int(sub["attempt"]),
                "submitted_utc": sub["submitted_utc"], "collected_utc": stamp(), "status": status,
                "timestamps": metrics.get("timestamps"), "usage": metrics.get("usage"),
                "usage_note": "as reported at collection; the service may still be computing it",
                "options_sent": sub["options_sent"], "program_id": sub.get("program_id"),
                "versions_at_submission": sub["versions"], "versions_at_collection": versions(),
                "calibration_at_submission": sub["calibration_at_submission"]}
        if not job.done():
            try:
                reason = redact(str(job.error_message() or ""), forms)[:300]
            except Exception as exc:
                reason = f"unavailable: {type(exc).__name__}"
            rec = {"failure_record": True, "repetition": rep, "meta": meta, "error_message": reason,
                   "rule": "Addendum 2, item 6: executed if the service reports device usage above zero or a "
                           "running time stamp; otherwise rejected before execution. The lead records the "
                           "classification in the submit record after the owner has seen this record."}
            return finish(rec, forms, out_path)
        result = job.result()
        if len(result) != len(ORDER):
            raise Refused(f"FAILED: {len(result)} results returned, {len(ORDER)} expected")
        try:
            used = sorted({q for c in sub["circuits"] for q in c["active_physical_qubits"]})
            meta["calibration_at_run_time"] = calibration(job.backend(), used, props=job.properties(),
                                                          source="properties recorded with the job")
        except Exception as exc:
            meta["calibration_at_run_time"] = {"note": f"unavailable: {type(exc).__name__}"}
        runs = []
        for i, (M, t) in enumerate(ORDER):
            circ = next(c for c in sub["circuits"] if c["sites"] == M and c["time"] == t)
            raw, conv = counts_of(result[i], M)
            runs.append({"sites": M, "time": t, "repetition": rep, "shots": SHOTS, "counts": conv,
                         "counts_as_returned": raw, "meta": dict(meta, circuit=circ)})
        rec = {"bit_order": "site0-left", "returned_bit_order": RETURNED_ORDER, "runs": runs}
    except Refused:
        raise
    except Exception as exc:
        raise Refused(safe_error(exc, forms))
    return finish(rec, forms, out_path)


def merge(paths):
    runs, seen = [], set()
    for p in paths:
        with open(p) as fh:
            d = json.load(fh)
        if d.get("bit_order") != "site0-left" or "runs" not in d:
            raise Refused(f"REFUSED: {os.path.basename(p)} is not a result file")
        for r in d["runs"]:
            key = (int(r["sites"]), str(r["time"]), int(r["repetition"]))
            if key in seen:
                raise Refused(f"REFUSED: the run {key} occurs twice")
            seen.add(key)
            runs.append(r)
    want = {(M, t, r) for M, t in ORDER for r in range(1, REPETITIONS + 1)}
    gates = [{"sites": r["sites"], "time": r["time"], "repetition": r["repetition"],
              "two_qubit_gates": r["meta"]["circuit"]["two_qubit_gates"],
              "section4": r["meta"]["circuit"]["two_qubit_gates_section4"],
              "within_10_percent": r["meta"]["circuit"]["within_10_percent_of_section4"]} for r in runs]
    return {"bit_order": "site0-left", "returned_bit_order": RETURNED_ORDER,
            "complete": seen == want, "missing": sorted(want - seen), "gate_count_comparison": gates,
            "runs": sorted(runs, key=lambda r: (r["repetition"], r["sites"], float(r["time"])))}


def finish(rec, forms, out_path):
    text = json.dumps(rec, indent=1, sort_keys=True, default=str)
    for s in forms:
        if s in text:
            raise Refused("REFUSED TO PRINT: a record contained a credential; this is a defect of the script")
    if out_path:
        with open(out_path, "w") as fh:
            fh.write(text + "\n")
    return text


def main(argv=None):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("rehearse")
    a.add_argument("fake_name")
    a = sub.add_parser("dryrun")
    a.add_argument("--out", default="")
    a = sub.add_parser("submit")
    a.add_argument("repetition", type=int, choices=range(1, REPETITIONS + 1))
    a.add_argument("attempt", type=int, nargs="?", default=1, choices=range(1, 10))
    a.add_argument("--out", default="")
    a = sub.add_parser("collect")
    a.add_argument("repetition", type=int, choices=range(1, REPETITIONS + 1))
    a.add_argument("--out", default="")
    a = sub.add_parser("merge")
    a.add_argument("files", nargs="+")
    args = ap.parse_args(argv)
    record = os.path.join(HERE, "records", "submitted.json")
    try:
        if args.cmd == "rehearse":
            text = json.dumps(rehearse(args.fake_name), indent=1, sort_keys=True)
        elif args.cmd == "dryrun":
            text = dryrun(args.out)
        elif args.cmd == "submit":
            text = submit(args.repetition, args.attempt, record, args.out)
        elif args.cmd == "collect":
            text = collect(args.repetition, record, args.out)
        else:
            text = json.dumps(merge(args.files), indent=1, sort_keys=True)
    except Refused as exc:
        print(str(exc))
        return 1
    except Exception as exc:                       # never let a raw trace reach a public log
        print(f"FAILED: {type(exc).__name__} (text withheld)")
        return 1
    print(text)
    print("sha256 of the record text above (with its final newline): "
          + hashlib.sha256((text + "\n").encode()).hexdigest())
    return 0


if __name__ == "__main__":
    sys.exit(main())
