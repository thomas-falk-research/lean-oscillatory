# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Command line: python -m oscint_cert {make,check,kinds} ...   JSON on stdout, diagnostics on stderr.

Exit codes: 0 CERTIFIED (check) or certificate written (make); 1 REJECTED; 2 UNRESOLVED; 3 usage or input error.
"""
import argparse
import json
import sys

from . import cert as C
from . import rational as R


def main(argv=None):
    p = argparse.ArgumentParser(prog="oscint_cert", description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    mk = sub.add_parser("make", help="compute a certificate (not trusted until checked)")
    mk.add_argument("kind", choices=sorted(C.KINDS))
    mk.add_argument("--inputs", required=True, help="JSON object; rationals as strings such as \"7/2\" or \"0.25\"")
    mk.add_argument("--statements", required=True, help="path to stamps/statements.json")
    mk.add_argument("--digits", type=int, default=30)
    ck = sub.add_parser("check", help="check a certificate; the only command whose verdict may be CERTIFIED")
    ck.add_argument("certificate", help="path to a certificate, or - for stdin")
    ck.add_argument("--statements", required=True)
    ck.add_argument("--digits", type=int, default=30)
    sub.add_parser("kinds", help="list certificate kinds, their statements and assumptions")
    a = p.parse_args(argv)
    try:
        if a.cmd == "kinds":
            out = {k: {"statement": lab, "assumptions": [{"key": x, "text": C.ASSUMPTIONS[x]} for x in asm]}
                   for k, (lab, asm) in sorted(C.KINDS.items())}
            print(json.dumps(out, indent=1, sort_keys=True))
            return 0
        if not 10 <= a.digits <= 200:
            raise C.CertError("--digits must be between 10 and 200")
        statements, sha = C.load_statements(a.statements)
        if a.cmd == "make":
            print(json.dumps(C.make(a.kind, json.loads(a.inputs), statements, a.digits), indent=1, sort_keys=True))
            return 0
        raw = sys.stdin.read() if a.certificate == "-" else open(a.certificate, encoding="utf-8").read()
        try:
            cert = json.loads(raw)
        except json.JSONDecodeError as e:
            cert = None
            v = C._verdict("REJECTED", {}, [f"not JSON: {e.msg}"])
        if cert is not None:
            v = C.check(cert, statements, sha, a.digits)
        print(json.dumps(v, indent=1, sort_keys=True))
        return {"CERTIFIED": 0, "REJECTED": 1, "UNRESOLVED": 2}[v["status"]]
    except R.Unresolved as e:
        print(f"oscint_cert: UNRESOLVED: {e}", file=sys.stderr)
        return 2
    except (C.CertError, OSError, json.JSONDecodeError, KeyError) as e:
        print(f"oscint_cert: error: {e}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
