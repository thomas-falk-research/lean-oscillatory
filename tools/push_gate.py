#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Which checks a push needs, decided from the paths it changes (docs/lessons.md, rule 18). Stdlib only, no network.

The decision is made by this script, not by judgement:
  quick    `make quick` (guard, statements-check, api-check, docs-check, build, axiom audit, statement types,
           Mathlib names, entry point). Required for every path that is not listed below as documentation or as a
           component with its own tests, and so for every path this script does not know.
  docs     `make docs-check` only: prose and records that no build step reads.
  python   `cd python && python3 -m unittest tests.test_cert`        (the certificate checker)
  rust     `cd rust/oscint-cert && cargo test --release --locked`    (the second checker)
A status claim is not documentation: docs/STATUS.md, README.md, CHANGELOG.md, the API index and the statement prose
require `quick`. CI on the pull request remains the authority; this gate is the fast local check before a push.

Usage: tools/push_gate.py [--base REV] [REPO]   print the required checks for what is not yet on REV
                                                 (default: the branch's upstream, else origin/main), plus
                                                 uncommitted changes
       tools/push_gate.py --run [REPO]           run them, in order; exit non-zero at the first failure
       tools/push_gate.py --self-test
"""
import fnmatch
import subprocess
import sys

# First match wins. Patterns use fnmatch on the whole path ("*" also crosses "/").
RULES = [
    ("quick", ["docs/STATUS.md", "README.md", "CHANGELOG.md", "docs/statements.md", "docs/api.json",
               "docs/api/*", "docs/release-notes/*", "docs/policy.md"]),
    ("docs", ["docs/*", "review/*", "*.md", "numerics/results-*.txt", "numerics/review/*", "LICENSES/*",
              "CITATION.cff", "codemeta.json", ".zenodo.json", "experiments/*"]),
    ("python", ["python/*"]),
    ("rust", ["rust/*"]),
]
COMMANDS = {
    "quick": ["make", "quick"],
    "docs": ["make", "docs-check"],
    "python": ["sh", "-c", "cd python && python3 -m unittest tests.test_cert"],
    "rust": ["sh", "-c", "cd rust/oscint-cert && cargo test --release --locked"],
}
ORDER = ["quick", "docs", "python", "rust"]


def classify(path):
    for kind, patterns in RULES:
        if any(fnmatch.fnmatchcase(path, p) for p in patterns):
            return kind
    return "quick"  # unknown paths, Lean sources, tools, stamps, examples, workflows, build files


def required(paths):
    """The checks for a set of changed paths and, per check, one path that calls for it."""
    why = {}
    for p in sorted(paths):
        why.setdefault(classify(p), p)
    if "quick" in why:
        why.pop("docs", None)  # `make quick` runs docs-check
    return [(k, why[k]) for k in ORDER if k in why]


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)


def changed_paths(repo, base=None):
    if base is None:
        up = git(repo, "rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}")
        base = up.stdout.strip() if up.returncode == 0 else "origin/main"
    diff = git(repo, "diff", "--name-only", f"{base}...HEAD")
    if diff.returncode != 0:
        raise SystemExit(f"push-gate: cannot diff against {base}: {diff.stderr.strip()}")
    paths = set(diff.stdout.split("\n")) - {""}
    for line in git(repo, "status", "--porcelain").stdout.split("\n"):
        if line:
            paths.add(line[3:].split(" -> ")[-1].strip('"'))
    return base, paths


def self_test():
    cases = [
        (["docs/progress/log.md", "review/x-answers.md"], ["docs"]),
        (["docs/progress/log.md", "docs/STATUS.md"], ["quick"]),                 # a status claim is not prose
        (["README.md"], ["quick"]),
        (["OscInt/Front/X.lean"], ["quick"]),
        (["docs/a.md", "tools/check_docs.py"], ["quick"]),
        (["some/new/place.bin"], ["quick"]),                                     # unknown: the strict check
        (["python/oscint_cert/cert.py", "docs/contract/certificate-v0.md"], ["docs", "python"]),
        (["rust/oscint-cert/src/num.rs"], ["rust"]),
        (["stamps/statements.json"], ["quick"]),
        (["Makefile"], ["quick"]),
        ([".github/workflows/ci.yml"], ["quick"]),
        (["numerics/results-x-2026-01-01.txt", "CONTRIBUTING.md"], ["docs"]),
        ([], []),
    ]
    ok = True
    for paths, want in cases:
        got = [k for k, _ in required(paths)]
        good = got == want
        ok = ok and good
        print(f"push-gate self-test: {'PASS' if good else 'FAIL'}: {paths} -> {got}")
    return ok


def main(argv):
    if "--self-test" in argv:
        return 0 if self_test() else 1
    base = argv[argv.index("--base") + 1] if "--base" in argv else None
    rest = [a for i, a in enumerate(argv) if not a.startswith("-") and (i == 0 or argv[i - 1] != "--base")]
    repo = rest[0] if rest else "."
    base, paths = changed_paths(repo, base)
    need = required(paths)
    print(f"push-gate: {len(paths)} changed path(s) against {base}")
    if not need:
        print("push-gate: nothing to check")
        return 0
    for kind, path in need:
        print(f"push-gate: REQUIRED {' '.join(COMMANDS[kind][-1:] if COMMANDS[kind][0] == 'sh' else COMMANDS[kind])}"
              f"    (because of {path})")
    if "--run" not in argv:
        return 0
    for kind, _ in need:
        r = subprocess.run(COMMANDS[kind], cwd=repo)
        if r.returncode != 0:
            print(f"push-gate: FAIL {kind} (exit {r.returncode})")
            return r.returncode
    print("push-gate: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
