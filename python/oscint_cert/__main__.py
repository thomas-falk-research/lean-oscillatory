# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Command line: python -m oscint_cert {make,check,kinds} ...   JSON on stdout, diagnostics on stderr.

Exit codes: 0 CERTIFIED (check) or certificate written (make); 1 REJECTED; 2 UNRESOLVED; 3 for the command line, an
unreadable file, an unusable or unexpected statement list, or a `make` that cannot produce a certificate.
"""
import argparse
import hashlib
import json
import sys

from . import cert as C
from . import rational as R


class _Parser(argparse.ArgumentParser):
    def error(self, message):  # argparse exits 2 by default, which is the code for UNRESOLVED
        self.print_usage(sys.stderr)
        print(f"oscint_cert: error: {message}", file=sys.stderr)
        raise SystemExit(3)


def main(argv=None):
    p = _Parser(prog="oscint_cert", description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True, parser_class=_Parser)
    mk = sub.add_parser("make", help="compute a certificate (not trusted until checked)")
    mk.add_argument("kind", choices=sorted(C.KINDS))
    mk.add_argument("--inputs", required=True, help="JSON object; rationals as strings such as \"7/2\" or \"0.25\"")
    mk.add_argument("--statements", required=True, help="path to stamps/statements.json")
    mk.add_argument("--digits", type=int, default=30)
    ck = sub.add_parser("check", help="check a certificate; the only command whose verdict may be CERTIFIED")
    ck.add_argument("certificate", help="path to a certificate, or - for stdin")
    ck.add_argument("--statements", required=True)
    ck.add_argument("--expect-statements-sha256", metavar="HEX",
                    help="refuse to check unless the statement list has this SHA-256 (from the release notes)")
    ck.add_argument("--digits", type=int, default=30, help="working precision in decimal digits, 10 to 200")
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
            try:
                cert = C.make(a.kind, C.loads_strict(a.inputs), statements, a.digits)
            except R.Unresolved as e:
                raise C.CertError(f"no certificate: beyond the supported range or budget: {e}") from None
            print(json.dumps(cert, indent=1, sort_keys=True))
            return 0
        want = a.expect_statements_sha256
        if want is not None and want.lower() != sha:
            raise C.CertError(f"the statement list has SHA-256 {sha}, not the expected {want}")
        raw = sys.stdin.buffer.read() if a.certificate == "-" else open(a.certificate, "rb").read()
        try:
            v = C.check(C.loads_strict(raw.decode("utf-8")), statements, sha, a.digits)
        except (ValueError, C.CertError, RecursionError) as e:  # JSONDecodeError, UnicodeDecodeError are ValueErrors
            v = C._verdict("REJECTED", {}, [f"not strict JSON in UTF-8: {e}"], {"statements_sha256": sha})
        v["statements_pinned"] = want is not None
        v["certificate_sha256"] = hashlib.sha256(raw).hexdigest()
        print(json.dumps(v, indent=1, sort_keys=True))
        return {"CERTIFIED": 0, "REJECTED": 1, "UNRESOLVED": 2}[v["status"]]
    except (C.CertError, OSError, ValueError, KeyError) as e:
        print(f"oscint_cert: error: {e}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
