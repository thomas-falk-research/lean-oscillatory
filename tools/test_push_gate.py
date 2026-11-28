#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Integration tests of tools/push_gate.py on temporary repositories (stdlib unittest, no network).

Every repository is created under tempfile with `git init`; the real repository is never touched. Git runs with
GIT_CONFIG_GLOBAL=/dev/null and GIT_CONFIG_NOSYSTEM=1, without inherited GIT_* variables and with LC_ALL=C, so the
user's configuration and language cannot change what is tested. Each repository has a Makefile whose `quick` and
`docs-check` targets only print a marker (FAKE-QUICK, FAKE-DOCS-CHECK); with PG_TEST_FAIL set, `docs-check` fails, and
with PG_TEST_TOUCH set it creates an untracked file, the race the gate must detect. Every negative case asserts the
exact exit status and a specific message (docs/lessons.md, 64b and 65).

Usage: python3 -I tools/test_push_gate.py      (or: python3 -I -m unittest discover -s tools -p test_push_gate.py)
"""
import contextlib
import importlib.util
import io
import os
import subprocess
import sys
import tempfile
import unittest

TOOL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "push_gate.py")
_spec = importlib.util.spec_from_file_location("push_gate", TOOL)
push_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(push_gate)

for _k in list(os.environ):
    if _k.startswith("GIT_") or _k in ("MAKEFLAGS", "MFLAGS", "MAKELEVEL", "PG_TEST_FAIL", "PG_TEST_TOUCH"):
        del os.environ[_k]
os.environ.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", LC_ALL="C",
                  GIT_CEILING_DIRECTORIES=os.path.realpath(tempfile.gettempdir()))

URL = "https://user:SECRET-TOKEN-123@example.invalid/repo.git"
MAKEFILE = (
    "quick:\n\t@echo FAKE-QUICK\n"
    "docs-check:\n\t@echo FAKE-DOCS-CHECK\n"
    '\t@if [ -n "$$PG_TEST_FAIL" ]; then exit 1; fi\n'
    '\t@if [ -n "$$PG_TEST_TOUCH" ]; then touch race-file; fi\n'
)
ODD_DOCS = [b"docs/a\tb.md", b"docs/new\nline.md", b'docs/q"uote.md', "docs/ünï.md".encode(), b"docs/\xff.md", b"docs/\xfe.md"]


class Repo:
    def __init__(self, path, object_format=None):
        self.path = path
        os.mkdir(path)
        self.git("init", "-q", "-b", "main", *([f"--object-format={object_format}"] if object_format else []))
        self.write("Makefile", MAKEFILE)
        self.write("docs/a.md", "a\n")
        self.write("OscInt/Front/X.lean", "theorem x : True := trivial\n")
        self.base = self.commit("base")

    def git(self, *args):
        r = subprocess.run(["git", "-C", self.path, *args], capture_output=True)
        if r.returncode != 0:
            raise AssertionError(f"git {args} failed: {r.stderr!r}")
        return r.stdout.decode().strip()

    def write(self, rel, content):
        p = os.path.join(os.fsencode(self.path), os.fsencode(rel))
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "wb") as f:
            f.write(content.encode() if isinstance(content, str) else content)

    def commit(self, message):
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false",
                 "commit", "-q", "--allow-empty", "-m", message)
        return self.head()

    def head(self):
        return self.git("rev-parse", "HEAD")


def run_tool(*args, stdin=b"", **env):
    r = subprocess.run([sys.executable, "-I", TOOL, *args], input=stdin, capture_output=True,
                       env={**os.environ, **env})
    return r.returncode, r.stdout.decode("utf-8", "backslashreplace"), r.stderr.decode("utf-8", "backslashreplace")


def run_main(argv, stdin=b"", runner=None):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = push_gate.main(argv, stdin=io.BytesIO(stdin), runner=runner)
    return rc, out.getvalue(), err.getvalue()


class Base(unittest.TestCase):
    object_format = None

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.repo = Repo(os.path.join(self._tmp.name, "r"), self.object_format)
        self.r = self.repo.path

    def assertOutcome(self, result, code, *needles):
        rc, out, err = result
        both = out + err
        self.assertEqual(rc, code, both)
        for n in needles:
            self.assertIn(n, both)
        self.assertNotIn("SECRET-TOKEN", both)
        self.assertNotIn("Traceback", both)
        return both


class Advisory(Base):
    def gate(self, *extra, **env):
        return run_tool("--base", self.repo.base, *extra, self.r, **env)

    def test_docs_edit(self):
        self.repo.write("docs/a.md", "b\n")
        self.repo.commit("docs")
        both = self.assertOutcome(self.gate(), 0, "1 changed path(s)", "REQUIRED make docs-check    (because of docs/a.md)")
        self.assertNotIn("make quick", both)

    def test_lean_edit(self):
        self.repo.write("OscInt/Front/X.lean", "-- edit\n")
        self.repo.commit("lean")
        self.assertOutcome(self.gate(), 0, "REQUIRED make quick    (because of OscInt/Front/X.lean)")

    def test_deletion(self):
        self.repo.git("rm", "-q", "OscInt/Front/X.lean")
        self.repo.commit("delete")
        self.assertOutcome(self.gate(), 0, "1 changed path(s)", "REQUIRED make quick    (because of OscInt/Front/X.lean)")

    def test_rename_lean_to_docs_requires_quick(self):
        self.repo.git("mv", "OscInt/Front/X.lean", "docs/X.md")
        self.repo.commit("rename")
        both = self.assertOutcome(self.gate(), 0, "2 changed path(s)",
                                  "REQUIRED make quick    (because of OscInt/Front/X.lean)")
        self.assertNotIn("docs-check", both)

    def test_rename_docs_to_docs(self):
        self.repo.git("mv", "docs/a.md", "docs/b.md")
        self.repo.commit("rename")
        both = self.assertOutcome(self.gate(), 0, "2 changed path(s)", "REQUIRED make docs-check    (because of docs/a.md)")
        self.assertNotIn("make quick", both)

    def test_odd_names(self):
        for name in ODD_DOCS:
            self.repo.write(name, "x\n")
        self.repo.commit("odd docs")
        both = self.assertOutcome(self.gate(), 0, f"{len(ODD_DOCS)} changed path(s)", "REQUIRED make docs-check")
        self.assertNotIn("make quick", both)
        self.repo.write('OscInt/we"ird\tname.lean', "x\n")
        self.repo.commit("odd lean")
        self.assertOutcome(self.gate(), 0, "REQUIRED make quick    (because of 'OscInt/we\"ird\\tname.lean')")

    def test_diverged_base_takes_both_diffs(self):
        # The base has a Lean commit that HEAD lacks: `BASE...HEAD` lists only docs, `BASE HEAD` also the Lean file.
        self.repo.write("docs/a.md", "b\n")
        self.repo.commit("docs")
        self.repo.git("checkout", "-q", "-b", "other", self.repo.base)
        self.repo.write("OscInt/Front/X.lean", "-- other\n")
        self.repo.commit("other lean")
        self.repo.git("checkout", "-q", "main")
        self.assertOutcome(run_tool("--base", "other", self.r), 0, "2 changed path(s) against other",
                           "REQUIRED make quick    (because of OscInt/Front/X.lean)")

    def test_default_base_is_upstream(self):
        self.repo.git("branch", "up")
        self.repo.git("branch", "--set-upstream-to=up")
        self.repo.write("docs/a.md", "b\n")
        self.repo.commit("docs")
        self.assertOutcome(run_tool(self.r), 0, "1 changed path(s) against up", "REQUIRED make docs-check")

    def test_default_base_missing_fails_closed(self):
        self.assertOutcome(run_tool(self.r), 4, "push-gate: ERROR: cannot diff against origin/main")

    def test_dirty_without_run_is_reported(self):
        self.repo.write("OscInt/New.lean", "x\n")
        self.assertOutcome(self.gate(), 0, "1 of them uncommitted", "REQUIRED make quick    (because of OscInt/New.lean)")

    def dirty(self, kind):
        if kind == "staged":
            self.repo.write("docs/a.md", "staged\n")
            self.repo.git("add", "docs/a.md")
            return "docs/a.md"
        if kind == "unstaged":
            self.repo.write("docs/a.md", "unstaged\n")
            return "docs/a.md"
        self.repo.write("docs/sub/new\nfile.md", "untracked\n")  # in a new directory: --untracked-files=all
        return "'docs/sub/new\\nfile.md'"

    def test_run_refuses_dirty_tree(self):
        for kind in ("staged", "unstaged", "untracked"):
            with self.subTest(kind=kind):
                shown = self.dirty(kind)
                both = self.assertOutcome(self.gate("--run"), 3, "push-gate: REFUSED: uncommitted changes",
                                          f"push-gate:   dirty: {shown}")
                self.assertNotIn("FAKE-", both)
                self.repo.git("reset", "-q", "--hard")
                self.repo.git("clean", "-qfd")

    def test_run_passes(self):
        self.repo.write("docs/a.md", "b\n")
        self.repo.commit("docs")
        both = self.assertOutcome(self.gate("--run"), 0, "FAKE-DOCS-CHECK", "push-gate: PASS")
        self.assertNotIn("FAKE-QUICK", both)

    def test_run_failing_check(self):
        self.repo.write("docs/a.md", "b\n")
        self.repo.commit("docs")
        self.assertOutcome(self.gate("--run", PG_TEST_FAIL="1"), 2, "push-gate: FAIL docs (exit 2)")

    def test_race_end_to_end(self):
        self.repo.write("docs/a.md", "b\n")
        self.repo.commit("docs")
        both = self.assertOutcome(self.gate("--run", PG_TEST_TOUCH="1"), 5, "FAKE-DOCS-CHECK",
                                  "push-gate: FAIL: HEAD or the working tree changed while the checks ran",
                                  "push-gate:   dirty: race-file")
        self.assertNotIn("push-gate: PASS", both)

    def test_not_a_repository(self):
        plain = os.path.join(self._tmp.name, "plain")
        os.mkdir(plain)
        self.assertOutcome(run_tool(plain), 4, "push-gate: ERROR: git rev-parse failed (exit 128)",
                           "not a git repository")

    def test_usage_errors(self):
        self.assertOutcome(run_tool("--frobnicate", self.r), 2, "push-gate: usage error: unknown option --frobnicate")
        self.assertOutcome(run_tool("--base", "--run", self.r), 2, "usage error: --base needs a revision")
        self.assertOutcome(run_tool("--allow-new-branch", "main", self.r), 2, "applies to --pre-push only")


class PrePush(Base):
    def setUp(self):
        super().setUp()
        self.repo.write("docs/a.md", "b\n")
        self.head = self.repo.commit("docs")
        self.zero = "0" * len(self.head)

    def line(self, local_ref="refs/heads/main", local=None, remote_ref="refs/heads/main", remote=None):
        return f"{local_ref} {local or self.head} {remote_ref} {remote or self.repo.base}\n".encode()

    def gate(self, stdin, *extra, name="origin", **env):
        return run_tool("--pre-push", name, URL, *extra, self.r, stdin=stdin, **env)

    def test_docs_fast_forward(self):
        both = self.assertOutcome(self.gate(self.line()), 0, "push-gate: pre-push refs/heads/main", "1 changed path(s)",
                                  "REQUIRED make docs-check    (because of docs/a.md)")
        self.assertNotIn("make quick", both)

    def test_head_as_local_ref(self):
        self.assertOutcome(self.gate(self.line(local_ref="HEAD")), 0, "REQUIRED make docs-check")

    def test_lean_edit(self):
        self.repo.write("OscInt/Front/X.lean", "-- edit\n")
        self.head = self.repo.commit("lean")
        self.assertOutcome(self.gate(self.line()), 0, "REQUIRED make quick    (because of OscInt/Front/X.lean)")

    def test_rename_lean_to_docs_requires_quick(self):
        self.repo.git("mv", "OscInt/Front/X.lean", "docs/X.md")
        self.head = self.repo.commit("rename")
        both = self.assertOutcome(self.gate(self.line()), 0, "3 changed path(s)",
                                  "REQUIRED make quick    (because of OscInt/Front/X.lean)")
        self.assertNotIn("docs-check", both)

    def test_paths_are_the_pushed_range_only(self):
        # The remote already has the docs commit; only the Lean deletion after it is pushed.
        pushed_before = self.head
        self.repo.git("rm", "-q", "OscInt/Front/X.lean")
        self.head = self.repo.commit("delete")
        self.assertOutcome(self.gate(self.line(remote=pushed_before)), 0, "1 changed path(s)",
                           "REQUIRED make quick    (because of OscInt/Front/X.lean)")

    def test_odd_names(self):
        for name in ODD_DOCS:
            self.repo.write(name, "x\n")
        self.head = self.repo.commit("odd")
        both = self.assertOutcome(self.gate(self.line()), 0, f"{len(ODD_DOCS) + 1} changed path(s)",
                                  "REQUIRED make docs-check")
        self.assertNotIn("make quick", both)

    def test_run_passes(self):
        both = self.assertOutcome(self.gate(self.line(), "--run"), 0, "FAKE-DOCS-CHECK", "push-gate: PASS")
        self.assertNotIn("FAKE-QUICK", both)

    def test_empty_stdin(self):
        self.assertOutcome(self.gate(b""), 0, "push-gate: nothing to push")

    def test_head_is_not_local_oid(self):
        self.assertOutcome(self.gate(self.line(local=self.repo.base)), 3,
                           f"push-gate: REFUSED: the pushed object {self.repo.base} is not HEAD ({self.head})")

    def test_remote_oid_missing(self):
        missing = "1" * len(self.head)
        self.assertOutcome(self.gate(self.line(remote=missing)), 3,
                           f"REFUSED: the remote's commit {missing} for refs/heads/main is not in this repository",
                           "fetch it first: git fetch origin refs/heads/main")
        self.assertOutcome(self.gate(self.line(remote=missing), name=URL), 3, "git fetch <remote> refs/heads/main")

    def side_commit(self):
        self.repo.git("checkout", "-q", "-b", "side", self.repo.base)
        self.repo.write("side.txt", "s\n")
        side = self.repo.commit("side")
        self.repo.git("checkout", "-q", "main")
        return side

    def test_non_fast_forward(self):
        side = self.side_commit()
        self.assertOutcome(self.gate(self.line(remote=side)), 3,
                           f"REFUSED: non-fast-forward: the remote's commit {side} is not an ancestor of {self.head}")

    def test_new_branch(self):
        line = self.line(remote_ref="refs/heads/topic", remote=self.zero)
        self.assertOutcome(self.gate(line), 3, "REFUSED: refs/heads/topic is a new branch on the remote",
                           "--allow-new-branch BASE")
        self.assertOutcome(self.gate(line, "--allow-new-branch", self.repo.base), 0, "1 changed path(s)",
                           "REQUIRED make docs-check")
        side = self.side_commit()
        self.assertOutcome(self.gate(line, "--allow-new-branch", "side"), 3,
                           f"REFUSED: --allow-new-branch base {side} is not an ancestor of {self.head}")
        self.assertOutcome(self.gate(line, "--allow-new-branch", "nosuchref"), 3,
                           "REFUSED: --allow-new-branch nosuchref does not name a commit")

    def test_deletion(self):
        self.assertOutcome(self.gate(self.line(local_ref="(delete)", local=self.zero)), 3,
                           "REFUSED: deletion of refs/heads/main")

    def test_tag(self):
        self.repo.git("tag", "v1")
        line = self.line(local_ref="refs/tags/v1", remote_ref="refs/tags/v1", remote=self.zero)
        self.assertOutcome(self.gate(line), 3, "REFUSED: remote ref refs/tags/v1 is not a branch")
        line = self.line(local_ref="refs/tags/v1")
        self.assertOutcome(self.gate(line), 3, "REFUSED: local ref refs/tags/v1 is not a branch")

    def test_two_lines(self):
        self.assertOutcome(self.gate(self.line() + self.line(remote_ref="refs/heads/other")), 3,
                           "REFUSED: expected exactly one ref update on stdin, got 2")

    def test_malformed_lines(self):
        self.assertOutcome(self.gate(f"refs/heads/main {self.head}\n".encode()), 3,
                           "REFUSED: malformed pre-push line 1")
        self.assertOutcome(self.gate(self.line()[:-1]), 3, "the last line does not end with LF")
        self.assertOutcome(self.gate(self.line().replace(b"\n", b"\r\n")), 3, "not lowercase hexadecimal")

    def test_wrong_oid_width(self):
        self.assertOutcome(self.gate(self.line(remote=self.repo.base[:7])), 3,
                           "REFUSED: pre-push line 1: the remote object name has 7 hex digits, expected 40")

    def test_invalid_ref_name(self):
        self.assertOutcome(self.gate(self.line(remote_ref="refs/heads/a..b")), 3,
                           "REFUSED: refs/heads/a..b is not a valid ref name")

    def test_dirty_tree(self):
        for kind, shown in (("staged", "docs/a.md"), ("unstaged", "docs/a.md"), ("untracked", "OscInt/Sub/New.lean")):
            with self.subTest(kind=kind):
                if kind == "untracked":
                    self.repo.write("OscInt/Sub/New.lean", "x\n")
                else:
                    self.repo.write("docs/a.md", kind + "\n")
                    if kind == "staged":
                        self.repo.git("add", "docs/a.md")
                both = self.assertOutcome(self.gate(self.line(), "--run"), 3,
                                          "push-gate: REFUSED: uncommitted changes", f"push-gate:   dirty: {shown}")
                self.assertNotIn("FAKE-", both)
                self.repo.git("reset", "-q", "--hard")
                self.repo.git("clean", "-qfd")

    def test_not_a_repository(self):
        plain = os.path.join(self._tmp.name, "plain")
        os.mkdir(plain)
        self.assertOutcome(run_tool("--pre-push", "origin", URL, plain, stdin=self.line()), 4,
                           "push-gate: ERROR: git rev-parse failed (exit 128)", "not a git repository")

    def test_race_end_to_end(self):
        self.assertOutcome(self.gate(self.line(), "--run", PG_TEST_TOUCH="1"), 5,
                           "push-gate: FAIL: HEAD or the working tree changed while the checks ran",
                           "push-gate:   dirty: race-file")

    def argv(self):
        return ["--pre-push", "origin", URL, "--run", self.r]

    def test_race_fake_runner_dirties_tree(self):
        calls = []

        def runner(argv, cwd):
            calls.append((argv, os.path.realpath(cwd)))
            self.repo.write("docs/a.md", "changed by the check\n")
            return 0

        rc, out, err = run_main(self.argv(), self.line(), runner)
        self.assertEqual(calls, [(["make", "docs-check"], os.path.realpath(self.r))])
        self.assertEqual(rc, 5, out + err)
        self.assertIn("push-gate: FAIL: HEAD or the working tree changed while the checks ran", err)
        self.assertIn("push-gate:   dirty: docs/a.md", err)
        self.assertNotIn("push-gate: PASS", out)

    def test_race_fake_runner_moves_head(self):
        def runner(argv, cwd):
            self.repo.commit("made during the check")
            return 0

        rc, out, err = run_main(self.argv(), self.line(), runner)
        self.assertEqual(rc, 5, out + err)
        self.assertIn(f"push-gate:   HEAD was {self.head}, is {self.repo.head()}", err)

    def test_fake_runner_pass_and_no_call_when_refused(self):
        calls = []

        def runner(argv, cwd):
            calls.append(argv)
            return 0

        rc, out, _ = run_main(self.argv(), self.line(), runner)
        self.assertEqual((rc, calls), (0, [["make", "docs-check"]]))
        self.assertIn("push-gate: PASS", out)
        calls.clear()
        self.repo.write("untracked.txt", "x\n")
        rc, _, err = run_main(self.argv(), self.line(), runner)
        self.assertEqual((rc, calls), (3, []))
        self.assertIn("REFUSED: uncommitted changes", err)


class PrePushSha256(Base):
    object_format = "sha256"

    def test_widths(self):
        self.repo.write("docs/a.md", "b\n")
        head = self.repo.commit("docs")
        self.assertEqual(len(head), 64)
        good = f"refs/heads/main {head} refs/heads/main {self.repo.base}\n".encode()
        self.assertOutcome(run_tool("--pre-push", "origin", URL, self.r, stdin=good), 0, "REQUIRED make docs-check")
        sha1_width = f"refs/heads/main {head[:40]} refs/heads/main {self.repo.base[:40]}\n".encode()
        self.assertOutcome(run_tool("--pre-push", "origin", URL, self.r, stdin=sha1_width), 3,
                           "REFUSED: pre-push line 1: the local object name has 40 hex digits, expected 64")


class SelfTest(unittest.TestCase):
    def test_self_test_passes(self):
        rc, out, err = run_tool("--self-test")
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(out.count("push-gate self-test: PASS: "), len(out.splitlines()))
        self.assertGreaterEqual(len(out.splitlines()), 13)
        self.assertNotIn("FAIL", out)

    def test_self_test_fails_when_a_rule_is_broken(self):
        # docs/lessons.md 64b: a check is run once with a check forced to fail.
        saved = push_gate.RULES
        push_gate.RULES = [r for r in saved if r[0] != "docs"]
        try:
            rc, out, _ = run_main(["--self-test"])
        finally:
            push_gate.RULES = saved
        self.assertEqual(rc, 1)
        self.assertIn("push-gate self-test: FAIL: ['docs/progress/log.md', 'review/x-answers.md'] -> ['quick']", out)


if __name__ == "__main__":
    unittest.main()
