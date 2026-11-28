<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# The push gate made fail-closed: the change, its adversarial review, and the answers (2026-11-28, session 17)

Written by the lead. Tools only; no statement, proof or record of the trust chain is touched. The gate
(`tools/push_gate.py`, rule 18 of `docs/lessons.md`) is a local convenience that decides from the changed paths which
checks a push needs. CI on the pull request remains the authority, and nothing here weakens a server-side check.

## 1. Why

The post-K2 packet (`review/2026-11-28-postK2-packet-answers.md`) reported, and the lead reproduced with the packet's
synthetic fixture, two defects of the gate as merged:
- a rename from a Lean source to `docs/X.md` listed only the destination, so the gate asked for `make docs-check`
  although a Lean file left the tree;
- the checks ran on the working tree, so an uncommitted fix could make the gate pass for a commit that lacks it; git
  failures (for example of `git status`) were ignored.

## 2. The change (commits c46c8e8 and 099e6c9 on this branch)

Written by an engineering agent of the lead's model family in its own git worktree (brief SHA-256
e7652ed2cfc8603a82d43a6e3216a82f6c664e06b4b423517f9ebb75097ecc1a), then reviewed (section 3) and fixed by the same
agent. Behaviour as merged here:
- paths come from `--no-renames -z` diffs (both sides of a rename), from the exact snapshots `BASE HEAD` and, so that
  a file changed and changed back is still seen, from `git log -m --no-renames --name-only -z BASE..TIP`;
- every git failure exits 4; an upstream that is configured but does not resolve exits 4 instead of falling back
  silently; the fallback to `origin/main` is printed;
- `--run` refuses a dirty tree (staged, unstaged, untracked) and any index entry hidden from `git status`
  (assume-unchanged, skip-worktree), and re-checks HEAD and status after the checks (race);
- a new `--pre-push REMOTE URL` mode implements Git's pre-push protocol for exactly one fast-forward branch update
  whose local oid is HEAD; tags, deletions, several refs, malformed lines, wrong oid widths, missing objects and
  partial clones are refused; a new branch is compared with its merge-base with `refs/remotes/<remote>/main`; the URL
  is never printed; no input reaches a shell;
- paths under `stamps/`, `OscInt/`, `Blueprint/`, `Challenge/`, `tools/`, `examples/`, `.github/` need `make quick`
  even when they end in `.md`; a change to the gate itself always needs `make quick` and prints a warning;
- `tools/pre-push-hook.sh` is a wrapper a user may install by hand; nothing installs it;
- `.gitignore`: `.lake` and `/build` without the trailing slash, so the symlinked build directories of the gate
  worktree of lessons 68a are ignored;
- CI: the `tools` job runs `tools/test_push_gate.py` next to the self-test.

## 3. The adversarial review

One fresh-context reviewer of the lead's model family, launched 12:29:06Z on e8999e7 (brief SHA-256
1420b61bbb47d4a6aef342b2c150ef349345d355f02de6448d5b13c91dfa7d18), read-only on the agent's worktree, attacking in
temporary repositories. Verdict **ACCEPT WITH FIXES**, no BLOCKER. Findings in the lead's words and their answers:

| ID | Severity | Finding | Answer |
|---|---|---|---|
| M1 | MAJOR | A configured upstream whose remote-tracking ref is missing made `rev-parse @{u}` exit 128, which the gate read as "no upstream"; it then diffed against `origin/main` and could ask for docs-check only while a Lean file was outgoing (reproduced). | Fixed: upstream read from `for-each-ref`; configured but unresolvable exits 4; tested. |
| M2 | MAJOR | Files marked skip-worktree or assume-unchanged are invisible to `git status`, so `--run` could pass on working-tree content that is not the commit (reproduced). | Fixed: `git ls-files -v -z`, any tag other than `H` refuses; tested for both. |
| m1 | MINOR | `*.md` matched at any depth, so Markdown under `stamps/`, `OscInt/`, `tools/` needed docs-check only (pre-existing). | Fixed: code and stamp directories first in the quick rule. |
| m2 | MINOR | Only end snapshots were compared; a stamp file changed and restored across two commits was not seen. | Fixed: union with `git log` over the range. |
| m3 | MINOR | `--allow-new-branch HEAD` passed trivially, and the hook could not create a branch at all. | Fixed: merge-base with the remote's `main`; a given base must be contained in a remote-tracking ref. |
| m4 | MINOR | The hook runs the gate version being pushed, so a push could weaken its own gate. | Mitigated: a gate change always needs quick and is flagged; the residual risk (a reviewer must read such a change) is stated in the docstring. |
| m5 | MINOR | In a partial clone, object lookups fetched lazily over the network. | Fixed: partial clones refused; `GIT_NO_LAZY_FETCH=1` set (effective from git 2.45). |
| m6 | MINOR | The gate worktree of lessons 68a with a symlinked `.lake` was reported dirty. | Fixed in `.gitignore`. |
| m7 | MINOR | Test gaps (eight mutants survived). | Fixed: tests added; the agent's mutation run catches 36 of 37 planted mutations; the survivor removes a three-dot diff whose paths the new `git log` term already lists. |
| NITs | NIT | Option values starting with `-`, a NUL byte on stdin, exit-code collisions, stale counts in `docs/lessons.md`. | Fixed except the two below. |

Not done, and why:
- `docs/lessons.md` entry 54 says the self-test has 13 planted cases (now 46), and entry 35 says no automatic check
  exists. `docs/lessons.md` is a rule file; an edit to it is its own commit with the owner's decision (lessons 67c).
  Left for the owner.
- A failing check's exit code can coincide with a gate code (make exits 2, as a usage error does); the messages
  differ. Left as is.

## 4. Evidence run by the lead on this branch

- `python3 -I tools/push_gate.py --self-test`: 46 PASS, 0 FAIL. `python3 -I tools/test_push_gate.py`: 63 tests, OK.
- `make tools-test`: every Rust test result ok. `actionlint` v1.7.7 (the version `ci.yml` installs): exit 0.
  `shellcheck tools/pre-push-hook.sh`: clean. `reuse lint` (reuse 6.3.0): compliant, 2816 of 2816 files.
- End to end on the real tree, 13:06:32Z–13:13:39Z: `make push-gate RUN=1` under the session's exclusive Lean lock
  required `make quick` (tools and workflow changed) with both gate-changed warnings, ran it (axiom audit 2885 of
  2885 clean; entry point 200 names), passed its race check and printed `push-gate: PASS`, exit 0.

Not checked: macOS and case-insensitive filesystems, Windows, submodules, git versions other than 2.43.0 locally,
fsmonitor-valid index entries (`ls-files -v` without `-f` does not tag them).
