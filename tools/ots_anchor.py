#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Bitcoin anchors for the stamp manifests, kept out of place (docs/lessons.md, rule 21).

`make stamp` leaves two OpenTimestamps proofs in every stamp directory. At that moment they are *pending*: they prove
submission to a calendar server and depend on that server staying online. Some hours later the calendar has a
Bitcoin attestation; a proof upgraded with it needs only Bitcoin block headers. Stamp directories are history and
are never rewritten, so the upgraded proofs live in a directory of their own:

    anchors/ots/<stamp id>/<proof file name>      the upgraded copy (the original stays byte-identical in stamps/)
    anchors/ots/LOG.txt                           what `check` found, regenerated on every run

  upgrade [REPO]            copy each pending proof that has no upgraded copy yet, and ask its calendar for the
                            Bitcoin attestation (needs the network and the `ots` client of the pinned environment,
                            tools/requirements-ots.txt). A proof whose calendar has no attestation yet stays out.
  check [REPO] [--offline]  for every upgraded copy: it commits to SHA-256 of that stamp's manifest.txt, so does the
                            original, and (unless --offline) the Merkle root of each Bitcoin attestation equals the
                            block's merkle root at two independent public explorers. Writes the log. Exit 0 iff
                            every upgraded copy passes; pending stamps are listed, not failed.
  --self-test               planted defects must be caught: another manifest, a wrong Merkle root at one explorer,
                            a proof that is only pending.

What a passing check shows: the manifest existed no later than the block time (accurate to about two hours). What it
trusts: the opentimestamps library, the two explorers and the network path to them (inside a cloud container both
requests pass one proxy; `ots verify` against a local Bitcoin node removes that trust).
"""
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import time
import urllib.request

EXPLORERS = [("mempool.space", "https://mempool.space/api"), ("blockstream.info", "https://blockstream.info/api")]


def _lib():
    try:
        from opentimestamps.core.notary import BitcoinBlockHeaderAttestation, PendingAttestation
        from opentimestamps.core.serialize import StreamDeserializationContext
        from opentimestamps.core.timestamp import DetachedTimestampFile
    except ImportError:
        raise SystemExit("ots-anchor: the opentimestamps library is missing; install tools/requirements-ots.txt "
                         "into a virtual environment and run this script with its python")
    return DetachedTimestampFile, StreamDeserializationContext, BitcoinBlockHeaderAttestation, PendingAttestation


def read_proof(data):
    """(file digest, [(height, merkle root in display order)], [pending calendar URIs])."""
    Detached, Ctx, Btc, Pending = _lib()
    d = Detached.deserialize(Ctx(io.BytesIO(data)))
    blocks, pending = [], []
    for msg, att in d.timestamp.all_attestations():
        if isinstance(att, Btc):
            blocks.append((att.height, msg[::-1].hex()))
        elif isinstance(att, Pending):
            pending.append(att.uri)
    return d.file_digest, sorted(blocks), sorted(pending)


def fetch(url, tries=4):
    for k in range(tries):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "ots-anchor"}),
                                        timeout=30) as r:
                return r.read().decode()
        except OSError:
            if k == tries - 1:
                raise
            time.sleep(2 ** (k + 1))


def block_at(base, height, fetcher=fetch):
    h = fetcher(f"{base}/block-height/{height}").strip()
    b = json.loads(fetcher(f"{base}/block/{h}"))
    return b["merkle_root"], b["timestamp"]


def check_proof(proof, original, manifest, offline=False, fetcher=fetch):
    """(status, lines). status: OK, PENDING or FAIL."""
    want = hashlib.sha256(manifest).digest()
    lines = []
    try:
        digest, blocks, pending = read_proof(proof)
        odigest, _, _ = read_proof(original)
    except Exception as e:  # a proof that does not parse is a failure, whatever the library raises
        return "FAIL", [f"unreadable proof: {type(e).__name__}: {e}"]
    if digest != want or odigest != want:
        return "FAIL", ["the proof does not commit to SHA-256 of this stamp's manifest.txt"]
    if not blocks:
        return "PENDING", [f"no Bitcoin attestation yet (calendar: {', '.join(pending) or 'none named'})"]
    status = "OK"
    for height, root in blocks:
        if offline:
            lines.append(f"block {height}: merkle root {root} (not compared: --offline)")
            continue
        seen = []
        for name, base in EXPLORERS:
            try:
                got, t = block_at(base, height, fetcher)
                same = got == root
                seen.append(f"{name}: {'match' if same else 'MISMATCH'} (block time "
                            f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t))})")
                status = status if same else "FAIL"
            except Exception as e:
                seen.append(f"{name}: no answer ({type(e).__name__})")
                status = "FAIL"
        lines.append(f"block {height}: " + "; ".join(seen))
    return status, lines


def stamp_proofs(repo):
    root = os.path.join(repo, "stamps")
    for sid in sorted(os.listdir(root)):
        d = os.path.join(root, sid)
        if os.path.isdir(d) and os.path.isfile(os.path.join(d, "manifest.txt")):
            for f in sorted(os.listdir(d)):
                if f.endswith(".ots"):
                    yield sid, f


def upgrade(repo):
    ots = os.path.join(os.path.dirname(sys.executable), "ots")
    if not os.path.isfile(ots):
        ots = shutil.which("ots") or sys.exit("ots-anchor: no `ots` client next to this python or on PATH")
    done = waiting = already = 0
    for sid, f in stamp_proofs(repo):
        dst_dir = os.path.join(repo, "anchors", "ots", sid)
        dst = os.path.join(dst_dir, f)
        if os.path.isfile(dst):
            already += 1
            continue
        tmp = os.path.join(repo, "build", "ots-upgrade", sid)
        os.makedirs(tmp, exist_ok=True)
        work = os.path.join(tmp, f)
        shutil.copyfile(os.path.join(repo, "stamps", sid, f), work)
        subprocess.run([ots, "--no-bitcoin", "upgrade", work], capture_output=True, text=True)
        _, blocks, _ = read_proof(open(work, "rb").read())
        if blocks:
            os.makedirs(dst_dir, exist_ok=True)
            shutil.copyfile(work, dst)
            done += 1
        else:
            waiting += 1
    print(f"ots-anchor: upgraded {done}, already upgraded {already}, still pending at the calendar {waiting}")
    return 0


def check(repo, offline=False):
    out, bad, ok, pend = [], 0, 0, 0
    for sid, f in stamp_proofs(repo):
        original = open(os.path.join(repo, "stamps", sid, f), "rb").read()
        manifest = open(os.path.join(repo, "stamps", sid, "manifest.txt"), "rb").read()
        dst = os.path.join(repo, "anchors", "ots", sid, f)
        if not os.path.isfile(dst):
            pend += 1
            out.append(f"{sid} {f}: PENDING (no upgraded copy; original sha256 {hashlib.sha256(original).hexdigest()})")
            continue
        proof = open(dst, "rb").read()
        status, lines = check_proof(proof, original, manifest, offline)
        ok, bad, pend = ok + (status == "OK"), bad + (status == "FAIL"), pend + (status == "PENDING")
        out.append(f"{sid} {f}: {status}; manifest sha256 {hashlib.sha256(manifest).hexdigest()}; original proof "
                   f"sha256 {hashlib.sha256(original).hexdigest()}; upgraded proof sha256 "
                   f"{hashlib.sha256(proof).hexdigest()}")
        out.extend("    " + x for x in lines)
    head = [f"# anchors/ots/LOG.txt: written by tools/ots_anchor.py check{' --offline' if offline else ''} at "
            f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}",
            f"# {ok} anchored and checked, {pend} pending, {bad} failed. A block time dates a manifest to within "
            "about two hours.",
            "# Trust: the opentimestamps library, the explorers "
            + " and ".join(n for n, _ in EXPLORERS) + ", and the network path to them."]
    os.makedirs(os.path.join(repo, "anchors", "ots"), exist_ok=True)
    with open(os.path.join(repo, "anchors", "ots", "LOG.txt"), "w") as fh:
        fh.write("\n".join(head + out) + "\n")
    print(head[1][2:])
    return 1 if bad else 0


def self_test():
    Detached, _, Btc, Pending = _lib()
    from opentimestamps.core.op import OpSHA256
    from opentimestamps.core.serialize import StreamSerializationContext
    from opentimestamps.core.timestamp import Timestamp

    def proof(manifest, height=None, uri=None):
        t = Timestamp(hashlib.sha256(manifest).digest())
        node = t.ops.add(OpSHA256())
        if height is not None:
            node.attestations.add(Btc(height))
        if uri:
            node.attestations.add(Pending(uri))
        buf = io.BytesIO()
        Detached(OpSHA256(), t).serialize(StreamSerializationContext(buf))
        return buf.getvalue(), node.msg[::-1].hex()

    m = b"manifest\n"
    pending, _ = proof(m, uri="https://calendar.example")
    anchored, root = proof(m, height=7, uri="https://calendar.example")

    def explorer(answers):
        def f(url):
            name = "A" if "mempool" in url else "B"
            return "hash" if "/block-height/" in url else json.dumps({"merkle_root": answers[name], "timestamp": 0})
        return f

    results = [
        ("an anchored proof with both explorers agreeing passes",
         check_proof(anchored, pending, m, fetcher=explorer({"A": root, "B": root}))[0] == "OK"),
        ("another manifest is caught", check_proof(anchored, pending, b"other\n", offline=True)[0] == "FAIL"),
        ("a wrong Merkle root at one explorer is caught",
         check_proof(anchored, pending, m, fetcher=explorer({"A": root, "B": "00" * 32}))[0] == "FAIL"),
        ("a proof that is only pending is reported as pending, not as anchored",
         check_proof(pending, pending, m, offline=True)[0] == "PENDING"),
        ("an upgraded copy whose original commits to something else is caught",
         check_proof(anchored, proof(b"x\n", uri="u")[0], m, offline=True)[0] == "FAIL"),
        ("bytes that are not a proof are caught", check_proof(b"junk", pending, m, offline=True)[0] == "FAIL"),
    ]
    for name, ok in results:
        print(f"ots-anchor self-test: {'PASS' if ok else 'FAIL'}: {name}")
    return all(ok for _, ok in results)


if __name__ == "__main__":
    a = sys.argv[1:]
    if "--self-test" in a:
        sys.exit(0 if self_test() else 1)
    repo = next((x for x in a[1:] if not x.startswith("-")), ".")
    if a[:1] == ["upgrade"]:
        sys.exit(upgrade(repo))
    if a[:1] == ["check"]:
        sys.exit(check(repo, "--offline" in a))
    print(__doc__)
    sys.exit(2)
