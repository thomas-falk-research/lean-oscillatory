#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Documentation consistency checks (ROADMAP "Standing: repository hygiene"), stdlib only, no network.

Checks, each with a negative control run by --self-test:
  paths    every backticked repository path in a Markdown file exists in the tree, or in git history (the
           review records removed under lessons 46 are read with `git show 58a86d0:<path>`), or is listed in
           tools/check_docs_allow.txt as planned or as a deliberate future output (lessons 36);
  tables   every Markdown table row has the header's cell count (GitHub splits cells at an unescaped `|`, even in
           code spans);
  status   docs/STATUS.md has one row per statement of stamps/statements.json, and a row says
           "machine-checked" exactly when the statement has a proving theorem;
  pins     every `rev = "vX.Y.Z"` in README.md and docs/ names the same release as README.md (release notes under
           docs/release-notes/ document their own release and are skipped);
  privacy  no file under review/prompts/, and no file directly in review/ other than README.md and *-answers.md
           (owner privacy rule, lessons 46).

Usage: tools/check_docs.py [REPO]    exit 0 iff every check passes
       tools/check_docs.py --self-test   each negative control must be detected
"""
import json
import os
import re
import subprocess
import sys

PATH_TOKEN = re.compile(r"`([^`\n]+)`")
PATTERN = re.compile(r"[<>{}*?\[\]]|X\.Y\.Z|…|\.\.\.")
REV = re.compile(r'rev = "(v\d+\.\d+\.\d+)"')


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True, check=True).stdout


def tracked_files(repo):
    return [f for f in git(repo, "ls-files").split("\n") if f]


def path_candidates(line, tops):
    """Backticked tokens that name a repository path (first component a tracked top-level entry)."""
    out = []
    for m in PATH_TOKEN.finditer(line):
        s = m.group(1).strip()
        if " " in s or s.startswith(("http", "-", "$", "#", "@", "./.")):
            continue
        s = re.sub(r"(:\d+(-\d+)?(,\d+(-\d+)?)*|#.*)$", "", s).rstrip("/.,;")
        if s.startswith("./"):
            s = s[2:]
        if "/" not in s or PATTERN.search(s) or s.split("/")[0] not in tops:
            continue
        out.append(s)
    return out


def check_paths(repo, files, tracked, allow, in_history):
    tset = set(tracked)
    dirs = {f.rsplit("/", 1)[0] for f in tracked if "/" in f}
    dirs |= {d.rsplit("/", i)[0] for d in list(dirs) for i in range(1, d.count("/") + 1)}
    tops = {f.split("/")[0] for f in tracked}
    bad = []
    for f in files:
        fence = False
        for i, line in enumerate(open(os.path.join(repo, f), encoding="utf-8"), 1):
            if line.lstrip().startswith("```"):
                fence = not fence
                continue
            if fence:
                continue
            for s in path_candidates(line, tops):
                if s in tset or s in dirs or s in allow or in_history(s):
                    continue
                bad.append(f"{f}:{i}: `{s}` does not exist (not in the tree, not in history, not allowlisted)")
    return bad


def cells(row):
    return row.strip().replace("\\|", "").strip("|").count("|") + 1


def check_tables(repo, files):
    bad = []
    for f in files:
        lines = open(os.path.join(repo, f), encoding="utf-8").read().split("\n")
        i, fence = 0, False
        while i < len(lines):
            if lines[i].lstrip().startswith("```"):
                fence = not fence
            if (not fence and lines[i].lstrip().startswith("|") and i + 1 < len(lines)
                    and re.match(r"^\s*\|?\s*:?-{3,}", lines[i + 1])):
                n = cells(lines[i])
                j = i + 2
                while j < len(lines) and lines[j].lstrip().startswith("|"):
                    if cells(lines[j]) != n:
                        bad.append(f"{f}:{j + 1}: {cells(lines[j])} cells, header has {n} (escape `|` as `\\|`)")
                    j += 1
                i = j
                continue
            i += 1
    return bad


def status_rows(text):
    rows = {}
    for line in text.split("\n"):
        if line.startswith("| ") and not line.startswith(("| Statement", "|---")):
            c = [x.strip() for x in line.strip().strip("|").split("|")]
            rows[c[0].split()[0]] = c
    return rows


def check_status(statements, status_text):
    rows, bad = status_rows(status_text), []
    labels = set()
    for s in statements:
        lab = s["label"]
        key = "S1" if lab in ("S1.1", "S1.2", "S1.3") else lab
        labels.add(key)
        r = rows.get(key)
        if not r:
            bad.append(f"docs/STATUS.md: no row for {lab}")
            continue
        if r[-1].startswith("machine-checked") != bool(s.get("proved_by")):
            bad.append(f"docs/STATUS.md: row {key} says {r[-1][:30]!r} but proved_by is {s.get('proved_by')!r}")
    for extra in sorted(set(rows) - labels):
        bad.append(f"docs/STATUS.md: row {extra} has no statement in stamps/statements.json")
    return bad


def check_pins(texts):
    readme = REV.findall(texts.get("README.md", ""))
    if not readme:
        return ["README.md: no `rev = \"vX.Y.Z\"` pin"]
    want = readme[0]
    return [f"{f}: pins {v}, README.md pins {want}" for f, t in sorted(texts.items()) for v in REV.findall(t) if v != want]


def check_privacy(tracked):
    bad = [f"{f}: prompts are not committed (lessons 46)" for f in tracked if f.startswith("review/prompts/")]
    for f in tracked:
        if f.startswith("review/") and f.count("/") == 1 and f != "review/README.md" and not f.endswith("-answers.md"):
            bad.append(f"{f}: only README.md and *-answers.md belong directly in review/ (lessons 46)")
    return bad


def run(repo):
    tracked = tracked_files(repo)
    md = [f for f in tracked if f.endswith(".md") and not f.startswith("review/calibration/")]
    allow_file = os.path.join(repo, "tools/check_docs_allow.txt")
    allow = set()
    if os.path.exists(allow_file):
        allow = {ln.split("#")[0].strip() for ln in open(allow_file, encoding="utf-8")} - {""}

    def in_history(p):
        return bool(git(repo, "log", "--all", "--format=%H", "-1", "--", p).strip())

    statements = json.load(open(os.path.join(repo, "stamps/statements.json")))["statements"]
    status_text = open(os.path.join(repo, "docs/STATUS.md"), encoding="utf-8").read()
    texts = {f: open(os.path.join(repo, f), encoding="utf-8").read() for f in md
             if f == "README.md" or (f.startswith("docs/") and not f.startswith("docs/release-notes/"))}
    results = {
        "paths": check_paths(repo, md, tracked, allow, in_history),
        "tables": check_tables(repo, md),
        "status": check_status(statements, status_text),
        "pins": check_pins(texts),
        "privacy": check_privacy(tracked),
    }
    ok = True
    for name, bad in results.items():
        for b in bad:
            print(f"{name}: {b}")
        print(f"docs-check {name}: {'PASS' if not bad else 'FAIL'} ({len(bad)} problem(s))")
        ok = ok and not bad
    return ok


def self_test():
    """Each check must reject a crafted defect (lessons 18: a control on the exact path the check exists for)."""
    import tempfile
    results = []
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "docs"))
        with open(os.path.join(d, "docs/a.md"), "w") as fh:
            fh.write("See `docs/a.md` and `stamps/api.json`.\n| x | y |\n|---|---|\n| `a|b` | c |\n")
        tracked = ["docs/a.md", "stamps/statements.json"]
        bad = check_paths(d, ["docs/a.md"], tracked, set(), lambda p: False)
        results.append(("paths flags a never-existing path", len(bad) == 1 and "stamps/api.json" in bad[0]))
        results.append(("paths accepts a path found in history",
                        not check_paths(d, ["docs/a.md"], tracked, set(), lambda p: True)))
        results.append(("tables flags a code-span pipe", len(check_tables(d, ["docs/a.md"])) == 1))
    st = [{"label": "S9", "proved_by": None}, {"label": "S8", "proved_by": "OscInt.x"}]
    status = "| S9 | x | machine-checked |\n| S8 | x | stated |\n| S7 | x | stated |\n"
    results.append(("status flags proved/row mismatches and an orphan row", len(check_status(st, status)) == 3))
    results.append(("pins flags a stale pin",
                    len(check_pins({"README.md": 'rev = "v0.4.0"', "docs/d.md": 'rev = "v0.3.0"'})) == 1))
    results.append(("privacy flags a prompt and a verbatim report",
                    len(check_privacy(["review/prompts/p.md", "review/2026-01-01-X-pre-proof-A.md",
                                       "review/README.md", "review/2026-01-01-X-answers.md"])) == 2))
    for name, ok in results:
        print(f"docs-check self-test: {'PASS' if ok else 'FAIL'}: {name}")
    return all(ok for _, ok in results)


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(0 if self_test() else 1)
    repo = next((a for a in sys.argv[1:] if not a.startswith("-")), ".")
    sys.exit(0 if run(repo) else 1)
