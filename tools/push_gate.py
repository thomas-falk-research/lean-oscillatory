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
require `quick`, and so does every path under stamps/, OscInt/, Blueprint/, Challenge/, tools/, examples/ and
.github/, Markdown included. CI on the pull request remains the authority; this gate is the fast local check before
a push.

Usage: tools/push_gate.py [--base REV] [REPO]   print the required checks for what is not yet on REV
                                                 (default: the branch's configured upstream; with none configured
                                                 or a detached HEAD, origin/main, and the fallback is printed),
                                                 plus uncommitted changes
       tools/push_gate.py --run [REPO]           run them, in order; exit non-zero at the first failure.
                                                 Refuses a tree that is not the commit (see Snapshot).
       tools/push_gate.py --pre-push REMOTE_NAME REMOTE_URL [--allow-new-branch BASE] [--run] [REPO]
                                                 Git's pre-push protocol on stdin; the checks for exactly the
                                                 commits pushed (see below)
       tools/push_gate.py --self-test

Paths. Every diff is `git diff --no-renames --name-only -z`, so a rename lists both the old and the new path (a Lean
source moved to docs/ still requires `quick`); names are read NUL-separated and decoded with os.fsdecode, so tabs,
newlines, quotes and bytes that are not UTF-8 survive. To the diff of the two end snapshots is added every path that
any commit in between touched (`git log -m --no-renames --format= --name-only -z BASE..TIP`), so a file changed and
changed back still counts. The advisory mode diffs both `BASE HEAD` and `BASE...HEAD` and adds `git status
--porcelain=v1 -z --untracked-files=all --no-renames`.

Snapshot. `--run` and the pre-push mode refuse a working tree that may differ from the commit: any entry of that
status command, and any index entry that `git ls-files -v` tags other than `H` (assume-unchanged, lower case, or
skip-worktree, `S`), which `git status` does not compare. After the checks, HEAD and both are read again and the gate
fails if anything changed. A partial clone (`extensions.partialClone`) is refused, since looking up an object could
fetch it; every git call also runs with GIT_NO_LAZY_FETCH=1.

Pre-push mode (fail closed). Stdin carries `<local ref> SP <local oid> SP <remote ref> SP <remote oid> LF` per ref.
Empty stdin: nothing to push, exit 0. Otherwise exactly one line, which must update a branch (`refs/heads/...`, valid
for `git check-ref-format`; the local ref may also be `HEAD`); the local oid must be HEAD; deletions, tags, several
lines, malformed lines, NUL bytes and object names of the wrong width (sha1 or sha256, from `git rev-parse
--show-object-format`) are refused. The remote oid must already be in the repository (nothing is fetched; the refusal
prints the fetch command) and must be an ancestor of the local oid (non-fast-forward is refused). A new branch
(remote oid all zeros) is compared with the merge-base of the local oid and `refs/remotes/REMOTE_NAME/main`, when
REMOTE_NAME is a plain name and that ref exists; `--allow-new-branch BASE` replaces that base by a commit that must
be an ancestor of HEAD and be contained in some `refs/remotes/*` ref (so `HEAD` itself is refused unless the remote
already has it); otherwise a new branch is refused. The URL is never printed and is never passed to git.

The hook wrapper, not installed by anything in this repository: tools/pre-push-hook.sh. To use it, copy it by hand to
`$(git rev-parse --git-path hooks)/pre-push`; it runs `python3 -I tools/push_gate.py --pre-push "$@" --run`.
Residual risk: the hook runs the gate of the working tree, which is the version being pushed, so a push can weaken
its own gate. When tools/push_gate.py or tools/pre-push-hook.sh is among the changed paths, `quick` is required
whatever the rules say and a WARNING line names the file; the change itself needs a reviewer.

Exit status: 0 pass or nothing to do; 1 self-test failure; a failing check's own status (128+N for signal N);
2 usage error; 3 refused (tree not the commit, pre-push policy); 4 a git command failed, gave output this script
cannot parse, or the repository cannot be trusted to answer locally (unresolvable upstream, partial clone);
5 HEAD or the tree changed while the checks ran. Every git failure ends the run; none is ignored.
"""
import fnmatch
import os
import re
import subprocess
import sys

# First match wins. Patterns use fnmatch on the whole path ("*" also crosses "/").
RULES = [
    ("quick", ["stamps/*", "OscInt/*", "Blueprint/*", "Challenge/*", "tools/*", "examples/*", ".github/*",
               "docs/STATUS.md", "README.md", "CHANGELOG.md", "docs/statements.md", "docs/api.json",
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
GATE_FILES = ("tools/push_gate.py", "tools/pre-push-hook.sh")  # a change to the gate itself always requires quick

EXIT_USAGE = 2
EXIT_REFUSED = 3
EXIT_GIT = 4
EXIT_RACE = 5
OBJECT_WIDTHS = {"sha1": 40, "sha256": 64}
SAFE_REMOTE_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")
GIT_ENV = {"GIT_NO_LAZY_FETCH": "1"}


class GateError(Exception):
    """Ends the run with `code`; `message` and `details` are printed, one line each."""

    def __init__(self, code, message, details=()):
        super().__init__(message)
        self.code = code
        self.details = list(details)


def refused(message, details=()):
    return GateError(EXIT_REFUSED, f"REFUSED: {message}", details)


def git_error(message):
    return GateError(EXIT_GIT, f"ERROR: {message}")


def show(s):
    """A path or ref for one output line: printable UTF-8 as it is, anything else escaped by ascii()."""
    b = os.fsencode(s)
    try:
        t = b.decode("utf-8")
    except UnicodeDecodeError:
        return ascii(b)
    return t if t.isprintable() else ascii(t)


# ---------------------------------------------------------------- classifier (pure)

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
    gate = sorted(set(paths) & set(GATE_FILES))
    if gate:
        why.setdefault("quick", gate[0])  # whatever RULES say
    if "quick" in why:
        why.pop("docs", None)  # `make quick` runs docs-check
    return [(k, why[k]) for k in ORDER if k in why]


# ---------------------------------------------------------------- parsers (pure)

def split_nul(data, what):
    """The fields of NUL-terminated git output (bytes), decoded with os.fsdecode."""
    if not data:
        return []
    if not data.endswith(b"\0"):
        raise git_error(f"{what}: output is not NUL-terminated")
    fields = data[:-1].split(b"\0")
    if b"" in fields:
        raise git_error(f"{what}: empty field in output")
    return [os.fsdecode(f) for f in fields]


def parse_status(data):
    """Every path named by `git status --porcelain=v1 -z` output: both sides of a rename or copy entry."""
    fields = split_nul(data, "git status")
    paths, i = [], 0
    while i < len(fields):
        entry = fields[i]
        i += 1
        if len(entry) < 4 or entry[2] != " ":
            raise git_error(f"git status: malformed entry {show(entry)}")
        paths.append(entry[3:])
        if "R" in entry[:2] or "C" in entry[:2]:
            if i >= len(fields):
                raise git_error("git status: rename entry without its source path")
            paths.append(fields[i])
            i += 1
    return paths


def parse_ls_files_v(data):
    """(tag, path) of every `git ls-files -v -z` entry whose tag is not H: entries git status does not compare."""
    hidden = []
    for entry in split_nul(data, "git ls-files -v"):
        if len(entry) < 3 or entry[1] != " ":
            raise git_error(f"git ls-files -v: malformed entry {show(entry)}")
        if entry[0] != "H":
            hidden.append((entry[0], entry[2:]))
    return hidden


def parse_pre_push(data, width):
    """Git's pre-push stdin (bytes) as a list of (local ref, local oid, remote ref, remote oid)."""
    if b"\0" in data:
        raise refused("malformed pre-push input: it contains a NUL byte")
    text = os.fsdecode(data)
    if text == "":
        return []
    if not text.endswith("\n"):
        raise refused("malformed pre-push input: the last line does not end with LF")
    updates = []
    for n, line in enumerate(text[:-1].split("\n"), 1):
        fields = line.split(" ")
        if len(fields) != 4 or "" in fields:
            raise refused(f"malformed pre-push line {n}: expected '<local ref> <local oid> <remote ref> <remote oid>'")
        lref, loid, rref, roid = fields
        for side, oid in (("local", loid), ("remote", roid)):
            if not re.fullmatch(r"[0-9a-f]+", oid):
                raise refused(f"pre-push line {n}: the {side} object name is not lowercase hexadecimal")
            if len(oid) != width:
                raise refused(f"pre-push line {n}: the {side} object name has {len(oid)} hex digits, expected {width}")
        updates.append((lref, loid, rref, roid))
    return updates


def select_update(updates, width):
    """The single branch update the policy allows; the checks that need no repository."""
    if len(updates) != 1:
        raise refused(f"expected exactly one ref update on stdin, got {len(updates)}")
    lref, loid, rref, roid = updates[0]
    if loid == "0" * width:
        raise refused(f"deletion of {show(rref)}")
    if not rref.startswith("refs/heads/"):
        raise refused(f"remote ref {show(rref)} is not a branch (refs/heads/...)")
    if lref != "HEAD" and not lref.startswith("refs/heads/"):
        raise refused(f"local ref {show(lref)} is not a branch (refs/heads/...) or HEAD")
    return updates[0]


def safe_remote_name(name, url):
    """The remote's name when it is a plain configured name (not a URL, not the URL); else None."""
    return name if SAFE_REMOTE_NAME.fullmatch(name) and name != url else None


def parse_args(argv):
    opts = {"self_test": False, "run": False, "base": None, "pre_push": None, "allow_new_branch": None,
            "repo": None}
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--self-test":
            opts["self_test"] = True
        elif a == "--run":
            opts["run"] = True
        elif a in ("--base", "--allow-new-branch"):
            if i + 1 >= len(argv) or argv[i + 1] == "" or argv[i + 1].startswith("-"):
                raise GateError(EXIT_USAGE, f"usage error: {a} needs a revision that does not start with '-'")
            opts[a[2:].replace("-", "_")] = argv[i + 1]
            i += 1
        elif a == "--pre-push":
            if i + 2 >= len(argv) or any(v == "" or v.startswith("-") for v in argv[i + 1:i + 3]):
                raise GateError(EXIT_USAGE, "usage error: --pre-push needs REMOTE_NAME and REMOTE_URL, neither "
                                            "empty nor starting with '-'")
            opts["pre_push"] = (argv[i + 1], argv[i + 2])
            i += 2
        elif a.startswith("-"):
            raise GateError(EXIT_USAGE, f"usage error: unknown option {show(a)}")
        elif opts["repo"] is not None:
            raise GateError(EXIT_USAGE, "usage error: more than one REPO")
        else:
            opts["repo"] = a
        i += 1
    if opts["pre_push"] and opts["base"] is not None:
        raise GateError(EXIT_USAGE, "usage error: --base does not apply to --pre-push (the remote oid is the base)")
    if opts["allow_new_branch"] is not None and not opts["pre_push"]:
        raise GateError(EXIT_USAGE, "usage error: --allow-new-branch applies to --pre-push only")
    return opts


# ---------------------------------------------------------------- git (every failure ends the run)

def git(repo, *args, ok=(0,)):
    """Run git with an argument vector (no shell, no lazy fetch); a status outside `ok` raises."""
    try:
        r = subprocess.run(["git", "--no-optional-locks", "-C", repo, *args], capture_output=True,
                           stdin=subprocess.DEVNULL, env={**os.environ, **GIT_ENV})
    except (OSError, ValueError) as e:
        raise git_error(f"cannot run git: {e}")
    if r.returncode not in ok:
        err = "; ".join(show(x) for x in os.fsdecode(r.stderr).strip().splitlines()) or "no message"
        raise git_error(f"git {args[0]} failed (exit {r.returncode}): {err[:600]}")
    return r


def one_line(r, what, allow_empty=False):
    out = os.fsdecode(r.stdout)
    if allow_empty and out in ("", "\n"):
        return ""
    if not out.endswith("\n") or "\n" in out[:-1] or out == "\n":
        raise git_error(f"{what}: unexpected output {show(out)}")
    return out[:-1]


def open_repo(repo):
    """The top of the working tree; a partial clone is refused (an object lookup could fetch)."""
    top = one_line(git(repo, "rev-parse", "--show-toplevel"), "git rev-parse --show-toplevel")
    if git(top, "config", "--get", "extensions.partialClone", ok=(0, 1)).returncode == 0:
        raise git_error("this is a partial clone (extensions.partialClone is set): looking up an object could fetch "
                        "it from the network; run the gate in a full clone")
    return top


def object_width(repo):
    fmt = one_line(git(repo, "rev-parse", "--show-object-format"), "git rev-parse --show-object-format")
    if fmt not in OBJECT_WIDTHS:
        raise git_error(f"unknown object format {show(fmt)}")
    return OBJECT_WIDTHS[fmt]


def resolve_commit(repo, rev):
    """The commit `rev` names; None when it names none (rev-parse --verify --quiet exits 1)."""
    r = git(repo, "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}", ok=(0, 1))
    return one_line(r, "git rev-parse --verify") if r.returncode == 0 else None


def head_oid(repo):
    oid = resolve_commit(repo, "HEAD")
    if oid is None:
        raise git_error("HEAD does not name a commit")
    return oid


def is_ancestor(repo, a, b):
    return git(repo, "merge-base", "--is-ancestor", a, b, ok=(0, 1)).returncode == 0


def on_remote_tracking_ref(repo, oid):
    r = git(repo, "for-each-ref", "--contains", oid, "--format=%(refname)", "refs/remotes/")
    return r.stdout.strip() != b""


def upstream(repo):
    """(ref, display name) of the current branch's configured upstream, or (None, why there is none).

    A configured upstream that does not map to a ref or does not resolve is an error, never a reason to fall back."""
    r = git(repo, "symbolic-ref", "-q", "HEAD", ok=(0, 1))
    if r.returncode == 1:
        return None, "HEAD is detached"
    branch = one_line(r, "git symbolic-ref HEAD")
    short = branch[len("refs/heads/"):] if branch.startswith("refs/heads/") else branch
    configured = [k for k in ("remote", "merge")
                  if git(repo, "config", "--get", f"branch.{short}.{k}", ok=(0, 1)).returncode == 0]
    line = one_line(git(repo, "for-each-ref", "--format=%(upstream)%00%(upstream:short)", branch),
                    "git for-each-ref %(upstream)", allow_empty=True)
    full, _, display = line.partition("\0")
    if not full:
        if configured:
            raise git_error(f"branch {show(short)} has branch.{show(short)}.{configured[0]} set but no upstream ref "
                            "(is the remote's fetch refspec configured?); fix it or pass --base")
        return None, f"no upstream is configured for {show(short)}"
    if resolve_commit(repo, full) is None:
        raise git_error(f"the upstream {show(full)} of {show(short)} is configured but does not resolve to a commit; "
                        "fetch it or pass --base")
    return full, display or full


def dirty_paths(repo):
    r = git(repo, "status", "--porcelain=v1", "-z", "--untracked-files=all", "--no-renames",
            "--ignore-submodules=none")
    return parse_status(r.stdout)


def hidden_entries(repo):
    return parse_ls_files_v(git(repo, "ls-files", "-v", "-z").stdout)


def diff_paths(repo, *revs):
    r = git(repo, "diff", "--no-renames", "--no-color", "--no-ext-diff", "--ignore-submodules=none",
            "--name-only", "-z", *revs, "--")
    return split_nul(r.stdout, "git diff")


def log_paths(repo, base, tip):
    """Every path a commit in base..tip touched (merges against each parent): changes that were later reverted."""
    r = git(repo, "log", "-m", "--no-renames", "--no-color", "--no-ext-diff", "--ignore-submodules=none",
            "--format=", "--name-only", "-z", f"{base}..{tip}", "--")
    if r.stdout and not r.stdout.endswith(b"\0"):
        raise git_error("git log: output is not NUL-terminated")
    return [os.fsdecode(f) for f in r.stdout.split(b"\0") if f]


def check_ref_name(repo, ref):
    if git(repo, "check-ref-format", ref, ok=(0, 1)).returncode != 0:
        raise refused(f"{show(ref)} is not a valid ref name (git check-ref-format)")


def snapshot_problems(repo):
    """(reasons, details) why the working tree may not be the commit; both empty when it is."""
    dirty, hidden = sorted(set(dirty_paths(repo))), hidden_entries(repo)
    reasons = (["uncommitted changes"] if dirty else []) + (
        ["index entries marked assume-unchanged or skip-worktree, which git status does not compare"] if hidden else [])
    details = [f"dirty: {show(p)}" for p in dirty] + [f"hidden from git status ({t}): {show(p)}" for t, p in hidden]
    return reasons, details


def require_snapshot(repo):
    reasons, details = snapshot_problems(repo)
    if reasons:
        raise refused("; ".join(reasons) + "; the checks must run on a committed snapshot (commit them, or clear "
                      "the index flags)", details)


# ---------------------------------------------------------------- runner

def default_runner(argv, cwd):
    sys.stdout.flush()
    sys.stderr.flush()
    return subprocess.run(argv, cwd=cwd, stdin=subprocess.DEVNULL).returncode


def print_plan(need, paths):
    for p in sorted(set(paths) & set(GATE_FILES)):
        print(f"push-gate: WARNING: the gate itself changed ({p}); a hook runs the version being pushed, so "
              "`make quick` is required and the change needs a reviewer")
    for kind, path in need:
        print(f"push-gate: REQUIRED {' '.join(COMMANDS[kind][-1:] if COMMANDS[kind][0] == 'sh' else COMMANDS[kind])}"
              f"    (because of {show(path)})")


def run_checks(repo, need, head, runner):
    """Run the checks in order; afterwards HEAD, the status and the index flags must be what they were before."""
    for kind, _ in need:
        try:
            rc = runner(COMMANDS[kind], repo)
        except OSError as e:
            print(f"push-gate: FAIL {kind} (cannot run: {e})")
            return 127
        if rc != 0:
            print(f"push-gate: FAIL {kind} (exit {rc})")
            return rc if rc > 0 else 128 - rc
    now_head = head_oid(repo)
    reasons, details = snapshot_problems(repo)
    if now_head != head or reasons:
        details = ([f"HEAD was {head}, is {now_head}"] if now_head != head else []) + details
        raise GateError(EXIT_RACE, "FAIL: HEAD or the working tree changed while the checks ran; the result does "
                                   "not describe the commit", details)
    print("push-gate: PASS")
    return 0


# ---------------------------------------------------------------- modes

def advisory(opts, runner):
    repo = open_repo(opts["repo"] or ".")
    base = display = opts["base"]
    if base is None:
        base, display = upstream(repo)
        if base is None:
            print(f"push-gate: {display}; the base falls back to origin/main")
            base = display = "origin/main"
    base_oid = resolve_commit(repo, base)
    if base_oid is None:
        raise git_error(f"cannot diff against {show(display)}: it does not name a commit")
    head = head_oid(repo)
    paths = (set(diff_paths(repo, base_oid, head)) | set(diff_paths(repo, f"{base_oid}...{head}"))
             | set(log_paths(repo, base_oid, head)))
    dirty, hidden = dirty_paths(repo), hidden_entries(repo)
    paths |= set(dirty) | {p for _, p in hidden}
    need = required(paths)
    print(f"push-gate: {len(paths)} changed path(s) against {show(display)}")
    if dirty:
        print(f"push-gate: {len(set(dirty))} of them uncommitted (--run refuses a dirty tree)")
    if hidden:
        print(f"push-gate: {len(hidden)} index entries marked assume-unchanged or skip-worktree (--run refuses them)")
    if not need:
        print("push-gate: nothing to check")
        return 0
    print_plan(need, paths)
    if not opts["run"]:
        return 0
    require_snapshot(repo)
    return run_checks(repo, need, head, runner)


def new_branch_base(repo, opts, remote_name, remote_url, rref, loid):
    """The base a new branch is compared with, and how it was chosen."""
    if opts["allow_new_branch"] is not None:
        rev = opts["allow_new_branch"]
        base = resolve_commit(repo, rev)
        if base is None:
            raise refused(f"--allow-new-branch {show(rev)} does not name a commit")
        if not is_ancestor(repo, base, loid):
            raise refused(f"--allow-new-branch base {base} is not an ancestor of {loid}")
        if not on_remote_tracking_ref(repo, base):
            raise refused(f"--allow-new-branch base {base} is on no remote-tracking ref (refs/remotes/*); the base "
                          "must be a commit the remote already has")
        return base, f"--allow-new-branch {show(rev)}"
    name = safe_remote_name(remote_name, remote_url)
    if name is None:
        raise refused(f"{show(rref)} is a new branch and the remote has no plain name to read "
                      "refs/remotes/<name>/main from; pass --allow-new-branch BASE")
    track = f"refs/remotes/{name}/main"
    tip = resolve_commit(repo, track)
    if tip is None:
        raise refused(f"{show(rref)} is a new branch and {track} does not exist here; fetch it first "
                      f"(git fetch {name} main) or pass --allow-new-branch BASE")
    mb = git(repo, "merge-base", loid, tip, ok=(0, 1))
    if mb.returncode == 1:
        raise refused(f"{show(rref)} is a new branch with no history in common with {track}")
    return one_line(mb, "git merge-base"), f"merge-base with {track}"


def pre_push(opts, stdin, runner):
    remote_name, remote_url = opts["pre_push"]  # the URL may carry a token: never printed, never passed on
    repo = open_repo(opts["repo"] or ".")
    width = object_width(repo)
    updates = parse_pre_push(stdin.read(), width)
    if not updates:
        print("push-gate: nothing to push")
        return 0
    lref, loid, rref, roid = select_update(updates, width)
    check_ref_name(repo, rref)
    if lref != "HEAD":
        check_ref_name(repo, lref)
    head = head_oid(repo)
    if loid != head:
        raise refused(f"the pushed object {loid} is not HEAD ({head}); check out the commit you push")
    if roid == "0" * width:
        base, how = new_branch_base(repo, opts, remote_name, remote_url, rref, loid)
        print(f"push-gate: new branch {show(rref)}: base {base[:12]} ({how})")
    else:
        if resolve_commit(repo, roid) is None:
            name = safe_remote_name(remote_name, remote_url) or "<remote>"
            raise refused(f"the remote's commit {roid} for {show(rref)} is not in this repository and nothing is "
                          f"fetched implicitly; fetch it first: git fetch {name} {rref}")
        base = roid
        if not is_ancestor(repo, base, loid):
            raise refused(f"non-fast-forward: the remote's commit {base} is not an ancestor of {loid}")
    require_snapshot(repo)
    paths = set(diff_paths(repo, base, loid)) | set(log_paths(repo, base, loid))
    need = required(paths)
    print(f"push-gate: pre-push {show(rref)} {base[:12]}..{loid[:12]}: {len(paths)} changed path(s)")
    if not need:
        print("push-gate: nothing to check")
        return 0
    print_plan(need, paths)
    if not opts["run"]:
        return 0
    return run_checks(repo, need, head, runner)


# ---------------------------------------------------------------- self-test

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
    cases += [
        (["OscInt/Front/X.lean", "docs/X.md"], ["quick"]),                       # both sides of a rename
        (["docs/old.md", "docs/new.md"], ["docs"]),
        (["docs/a\tb.md", "docs/new\nline.md", 'docs/q"uote.md', "docs/ünï.md"], ["docs"]),
        (["docs/x.md", os.fsdecode(b"OscInt/\xff.lean")], ["quick"]),
        (["stamps/s1/notes.md"], ["quick"]),                                     # Markdown inside a code tree
        (["OscInt/notes.md"], ["quick"]),
        (["Challenge/README.md"], ["quick"]),
        (["tools/README.md"], ["quick"]),
        (["tools/push_gate.py"], ["quick"]),                                     # the gate itself
    ]
    ok = True
    for paths, want in cases:
        got = [k for k, _ in required(paths)]
        good = got == want
        ok = ok and good
        print(f"push-gate self-test: {'PASS' if good else 'FAIL'}: {paths} -> {got}")

    z40, a40, b40 = "0" * 40, "a" * 40, "b" * 40

    def outcome(f):
        try:
            return ("ok", f())
        except GateError as e:
            return (e.code, str(e))

    def line(*fields):
        return (" ".join(fields) + "\n").encode()

    upd = ("refs/heads/main", a40, "refs/heads/main", b40)
    checks = [
        ("status: two entries, rename keeps both paths",
         lambda: parse_status(b"M  a.lean\0?? new\nline.md\0R  docs/X.md\0OscInt/X.lean\0"),
         ("ok", ["a.lean", "new\nline.md", "docs/X.md", "OscInt/X.lean"])),
        ("status: empty", lambda: parse_status(b""), ("ok", [])),
        ("status: not NUL-terminated", lambda: parse_status(b"M  a"), (EXIT_GIT, "not NUL-terminated")),
        ("status: malformed entry", lambda: parse_status(b"Ma\0"), (EXIT_GIT, "malformed entry")),
        ("nul fields: empty field", lambda: split_nul(b"a\0\0b\0", "git diff"), (EXIT_GIT, "empty field")),
        ("ls-files -v: H passes, h and S are hidden",
         lambda: parse_ls_files_v(b"H a\0h b c\0S d\0"), ("ok", [("h", "b c"), ("S", "d")])),
        ("ls-files -v: malformed entry", lambda: parse_ls_files_v(b"Ha\0"), (EXIT_GIT, "malformed entry")),
        ("pre-push: empty stdin", lambda: parse_pre_push(b"", 40), ("ok", [])),
        ("pre-push: one line", lambda: parse_pre_push(line(*upd), 40), ("ok", [upd])),
        ("pre-push: no final LF", lambda: parse_pre_push(line(*upd)[:-1], 40), (EXIT_REFUSED, "does not end with LF")),
        ("pre-push: three fields", lambda: parse_pre_push(line(*upd[:3]), 40), (EXIT_REFUSED, "malformed pre-push line 1")),
        ("pre-push: double space", lambda: parse_pre_push(line(upd[0], "", *upd[1:]), 40),
         (EXIT_REFUSED, "malformed pre-push line 1")),
        ("pre-push: NUL byte", lambda: parse_pre_push(line("refs/heads/m\0x", *upd[1:]), 40),
         (EXIT_REFUSED, "contains a NUL byte")),
        ("pre-push: sha1 width under sha256", lambda: parse_pre_push(line(*upd), 64),
         (EXIT_REFUSED, "has 40 hex digits, expected 64")),
        ("pre-push: upper-case hex", lambda: parse_pre_push(line(upd[0], "A" * 40, *upd[2:]), 40),
         (EXIT_REFUSED, "not lowercase hexadecimal")),
        ("policy: two updates", lambda: select_update([upd, upd], 40), (EXIT_REFUSED, "got 2")),
        ("policy: deletion", lambda: select_update([("(delete)", z40, "refs/heads/main", b40)], 40),
         (EXIT_REFUSED, "deletion of refs/heads/main")),
        ("policy: tag", lambda: select_update([("refs/tags/v1", a40, "refs/tags/v1", z40)], 40),
         (EXIT_REFUSED, "remote ref refs/tags/v1 is not a branch")),
        ("policy: HEAD as local ref", lambda: select_update([("HEAD", a40, "refs/heads/x", b40)], 40),
         ("ok", ("HEAD", a40, "refs/heads/x", b40))),
        ("remote name: plain", lambda: safe_remote_name("origin", "https://x.invalid/r"), ("ok", "origin")),
        ("remote name: a URL is not printed", lambda: safe_remote_name("https://t@x.invalid/r", "https://y.invalid/r"),
         ("ok", None)),
        ("args: unknown option", lambda: parse_args(["--rnu"]), (EXIT_USAGE, "unknown option --rnu")),
        ("args: --base without value", lambda: parse_args(["--base"]), (EXIT_USAGE, "--base needs a revision")),
        ("args: --pre-push URL starting with '-'", lambda: parse_args(["--pre-push", "origin", "-u"]),
         (EXIT_USAGE, "--pre-push needs REMOTE_NAME and REMOTE_URL")),
    ]
    for name, f, (want_code, want) in checks:
        code, got = outcome(f)
        good = code == want_code and (got == want if code == "ok" else want in got)
        ok = ok and good
        print(f"push-gate self-test: {'PASS' if good else 'FAIL'}: {name}")
    return ok


def main(argv, stdin=None, runner=None):
    try:
        opts = parse_args(argv)
        if opts["self_test"]:
            return 0 if self_test() else 1
        runner = runner or default_runner
        if opts["pre_push"]:
            return pre_push(opts, stdin if stdin is not None else sys.stdin.buffer, runner)
        return advisory(opts, runner)
    except GateError as e:
        sys.stdout.flush()
        print(f"push-gate: {e}", file=sys.stderr)
        for d in e.details:
            print(f"push-gate:   {d}", file=sys.stderr)
        return e.code


if __name__ == "__main__":
    sys.stdout.reconfigure(errors="backslashreplace")
    sys.stderr.reconfigure(errors="backslashreplace")
    sys.exit(main(sys.argv[1:]))
