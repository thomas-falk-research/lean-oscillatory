#!/usr/bin/env bash
# Release-pin check. Fails unless, for every release tag the user-facing files tell people to pin:
#   1. README.md itself pins a tag (a pin elsewhere does not count for README);
#   2. the tag exists in REMOTE, and the commit it points to (peeled) is exactly the commit recorded in
#      docs/release-notes/<tag>.commit (a full 40-hex hash, written in the commit after the release commit);
#   3. docs/release-notes/<tag>.md has exactly one table row each for stamps/statements.json and
#      tools/oscint_check.py, giving their SHA-256 AT THAT COMMIT, and every `--expect-sha256 <hex>` in the notes
#      equals the statements.json row;
#   4. the release commit is an ancestor of the checked-out commit (HEAD), so main never pins a release that main
#      does not contain (on a pull request, HEAD is the merge commit: the tag must be in what main becomes).
#      Needs full history (CI checks out with fetch-depth 0); a shallow clone fails this check, never skips it.
#   5. every raw 40-hex commit pin (`rev = "<hash>"`) names a commit contained in HEAD (which implies it exists), so a
#      commit pin cannot bypass checks 2–4 (adversarial review 2026-11-08, m1).
# Pins are recognised as `rev = "…"`/`rev = '…'` (any spacing), `@ "…"`, `@ git "…"`, with an optional
# `refs/tags/` prefix and an optional pre-release suffix; comment lines (`#`, `--`) are ignored; any other
# `rev =`/`@ git` line that is not a tag or a 40-hex commit is an error, never silently skipped.
# Files scanned: README.md, docs/policy.md, examples/consumer/lakefile.toml, examples/consumer-release/lakefile.toml.
#
# Usage: tools/check_release_pin.sh [REMOTE]     (default `origin`; CI passes the repository URL)
#        tools/check_release_pin.sh --self-test  (negative controls, no network)
# Exit: 0 pass; 1 a check failed; 2 usage or environment error. The tag is fetched into a private ref
# (refs/release-pin/<tag>), never into refs/tags, so a stale local tag cannot mask the remote one.
set -uo pipefail

TAGRE='v[0-9]+\.[0-9]+\.[0-9]+(-[0-9A-Za-z.]+)?'

# in_head COMMIT: COMMIT exists and is an ancestor of (or equal to) HEAD of the repository in the current directory.
in_head() { git merge-base --is-ancestor "$1" HEAD 2>/dev/null; }

# scan FILE: prints one line per pin: "tag <vX.Y.Z>" or "commit <hex>"; prints "bad <line>" for an unrecognised
# rev/@ git value. Comment lines are skipped.
scan() {
  local f=$1 line val
  [ -f "$f" ] || { echo "missing $f"; return 0; }
  while IFS= read -r line || [ -n "$line" ]; do
    case "$(sed -E 's/^[[:space:]]*//' <<<"$line")" in '#'*|'--'*) continue;; esac
    val=$(grep -oE "(rev[[:space:]]*=[[:space:]]*|@[[:space:]]*(git[[:space:]]+)?)[\"'][^\"']*[\"']" <<<"$line" \
      | sed -E "s/.*[\"']([^\"']*)[\"']$/\1/") || true
    [ -n "$val" ] || continue
    while IFS= read -r v; do
      v=${v#refs/tags/}
      if grep -qxE "$TAGRE" <<<"$v"; then echo "tag $v"
      elif grep -qxE '[0-9a-f]{40}' <<<"$v"; then echo "commit $v"
      else echo "bad $f: $line"; fi
    done <<<"$val"
  done < "$f"
}

# check_tag TAG REMOTE_COMMIT NOTES_DIR SHOW_CMD...: REMOTE_COMMIT is the peeled commit the remote tag points to
check_tag() {
  local tag=$1 rc_commit=$2 notes=$3; shift 3
  local nf="$notes/$tag.md" cf="$notes/$tag.commit" want f h rows n rc=0
  if [ -z "$rc_commit" ]; then
    echo "FAIL release pin: the docs tell users to pin $tag, but tag $tag does not exist in the repository."
    echo "     Fix: the owner publishes release $tag (steps in $nf), or the docs pin an existing tag."
    return 1
  fi
  [ -f "$nf" ] || { echo "FAIL release pin: tag $tag exists but its release notes $nf are missing."; return 1; }
  [ -f "$cf" ] || { echo "FAIL release pin: $cf (the full hash of the release commit) is missing."; return 1; }
  want=$(tr -d '[:space:]' < "$cf")
  grep -qxE '[0-9a-f]{40}' <<<"$want" || { echo "FAIL release pin: $cf does not hold one full commit hash."; return 1; }
  if [ "$rc_commit" != "$want" ]; then
    echo "FAIL release pin: tag $tag points to $rc_commit, but $cf records the release commit $want."
    return 1
  fi
  local sj=""
  for f in stamps/statements.json tools/oscint_check.py; do
    if ! h=$("$@" "$want:$f" | sha256sum | cut -d' ' -f1); then echo "FAIL release pin: cannot read $f at $want"; rc=1; continue; fi
    rows=$(grep -F "| \`$f\` |" "$nf" || true)
    n=$(grep -c . <<<"$rows" || true); [ -n "$rows" ] || n=0
    if [ "$n" -ne 1 ]; then echo "FAIL release pin: $nf has $n table rows for $f (exactly one required)."; rc=1; continue; fi
    if ! grep -qF "| \`$h\` |" <<<"$rows"; then
      echo "FAIL release pin: $f at $want has SHA-256 $h; the row in $nf says otherwise."; rc=1; fi
    [ "$f" = stamps/statements.json ] && sj=$h
  done
  local e
  for e in $(grep -oE -- '--expect-sha256[[:space:]]+[0-9a-f]+' "$nf" | awk '{print $2}'); do
    [ "$e" = "$sj" ] || { echo "FAIL release pin: $nf uses --expect-sha256 $e, not the statements.json row $sj."; rc=1; }
  done
  if ! "$ANCESTOR" "$want"; then
    echo "FAIL release pin: the release commit $want of $tag is not contained in the checked-out commit (HEAD)."
    echo "     Fix: merge the release branch into main before main pins $tag (or fetch full history: fetch-depth 0)."
    rc=1
  fi
  [ $rc -eq 0 ] && echo "ok   release pin $tag: tag -> $want (as recorded, contained in HEAD); notes give the SHA-256 of both pinned files there"
  return $rc
}

# run_checks NOTES_DIR LS_REMOTE_FILE SHOW_CMD... (pins read from the current directory's files)
run_checks() {
  local notes=$1 listing=$2; shift 2
  local files="README.md docs/policy.md examples/consumer/lakefile.toml examples/consumer-release/lakefile.toml"
  local all rc=0 f t c
  all=$(for f in $files; do scan "$f"; done)
  if grep -q '^missing ' <<<"$all"; then grep '^missing ' <<<"$all" | sed 's/^/FAIL release pin: /'; rc=1; fi
  if grep -q '^bad ' <<<"$all"; then grep '^bad ' <<<"$all" | sed 's/^bad /FAIL release pin: unrecognised pin: /'; rc=1; fi
  grep -q '^tag ' <<<"$(scan README.md)" || { echo "FAIL release pin: README.md pins no release tag (expected a line rev = \"vX.Y.Z\")."; rc=1; }
  for c in $(grep '^commit ' <<<"$all" | awk '{print $2}' | sort -u); do
    if "$ANCESTOR" "$c"; then echo "ok   commit pin $c is contained in HEAD"
    else echo "FAIL release pin: commit pin $c is not a commit contained in the checked-out commit (HEAD)."; rc=1; fi
  done
  for t in $(grep '^tag ' <<<"$all" | awk '{print $2}' | sort -u); do
    c=$(awk -v r="refs/tags/$t^{}" '$2==r{print $1}' "$listing")
    [ -n "$c" ] || c=$(awk -v r="refs/tags/$t" '$2==r{print $1}' "$listing")
    check_tag "$t" "$c" "$notes" "$@" || rc=1
  done
  return $rc
}

if [ "${1:-}" = "--self-test" ]; then
  T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
  fails=0
  C1=1111111111111111111111111111111111111111; C2=2222222222222222222222222222222222222222
  fake_show() { case "$1" in "$C1:stamps/statements.json") printf S;; "$C1:tools/oscint_check.py") printf C;;
                                 "$C2:stamps/statements.json") printf X;; "$C2:tools/oscint_check.py") printf C;; *) return 1;; esac; }
  NOT_IN_HEAD=$T/not-in-head
  C3=3333333333333333333333333333333333333333
  fake_anc() { [ ! -e "$NOT_IN_HEAD" ] && [ "$1" != "$C3" ]; }
  ANCESTOR=fake_anc
  hs=$(printf S | sha256sum | cut -d' ' -f1); hc=$(printf C | sha256sum | cut -d' ' -f1)
  setup() { rm -rf "$T/r"; mkdir -p "$T/r/docs/release-notes" "$T/r/examples/consumer" "$T/r/examples/consumer-release"
    printf 'rev = "v9.9.9"\n' > "$T/r/README.md"; : > "$T/r/docs/policy.md"
    : > "$T/r/examples/consumer/lakefile.toml"; : > "$T/r/examples/consumer-release/lakefile.toml"
    printf '| `stamps/statements.json` | `%s` |\n| `tools/oscint_check.py` | `%s` |\n--expect-sha256 %s\n' "$hs" "$hc" "$hs" \
      > "$T/r/docs/release-notes/v9.9.9.md"
    echo "$C1" > "$T/r/docs/release-notes/v9.9.9.commit"
    printf '%s\trefs/tags/v9.9.9\n' "$C1" > "$T/ls"; rm -f "$NOT_IN_HEAD"; }
  t() { local want=$1 name=$2; local got out; out=$(cd "$T/r" && run_checks docs/release-notes "$T/ls" fake_show 2>&1); got=$?
        [ "$got" -ne 0 ] && got=1
        if [ "$got" = "$want" ]; then echo "ok   self-test: $name"; else echo "FAIL self-test: $name (rc $got, want $want): $out"; fails=$((fails+1)); fi; }
  setup; t 0 "correct pin accepted"
  setup; : > "$T/ls"; t 1 "missing tag rejected"
  setup; printf '%s\trefs/tags/v9.9.90\n' "$C1" > "$T/ls"; t 1 "tag prefix (v9.9.90) does not satisfy v9.9.9"
  setup; printf '%s\trefs/tags/v9.9.9\n' "$C2" > "$T/ls"; t 1 "tag on another commit rejected (even with equal checker hash)"
  setup; printf 'aaaa\trefs/tags/v9.9.9\n%s\trefs/tags/v9.9.9^{}\n' "$C1" > "$T/ls"; t 0 "annotated tag peeled to the release commit"
  setup; rm "$T/r/docs/release-notes/v9.9.9.commit"; t 1 "missing commit record rejected"
  setup; rm "$T/r/docs/release-notes/v9.9.9.md"; t 1 "missing release notes rejected"
  setup; sed -i "s/$hc/0000/" "$T/r/docs/release-notes/v9.9.9.md"; t 1 "wrong checker hash rejected"
  setup; sed -i "0,/$hs/s//0000/" "$T/r/docs/release-notes/v9.9.9.md"; t 1 "wrong statements.json hash rejected"
  setup; printf '| `stamps/statements.json` | `deadbeef` |\n' >> "$T/r/docs/release-notes/v9.9.9.md"; t 1 "duplicate row rejected"
  setup; sed -i "s/--expect-sha256 $hs/--expect-sha256 0000/" "$T/r/docs/release-notes/v9.9.9.md"; t 1 "notes' --expect-sha256 disagreeing with the table rejected"
  setup; printf "rev = 'v9.9.8'\n" > "$T/r/README.md"; t 1 "single-quoted README pin of a missing tag rejected"
  setup; printf 'rev\t=  "v9.9.8"\n' > "$T/r/README.md"; t 1 "tab-spaced README pin of a missing tag rejected"
  setup; printf 'require "o" / "oscint" @ git "v9.9.8"\n' > "$T/r/README.md"; t 1 "@ git README pin of a missing tag rejected"
  setup; printf 'rev = "refs/tags/v9.9.8"\n' > "$T/r/README.md"; t 1 "refs/tags/ README pin of a missing tag rejected"
  setup; printf 'rev = "v9.9.8-rc1"\n' > "$T/r/README.md"; t 1 "pre-release README pin of a missing tag rejected"
  setup; printf '# rev = "v9.9.9"\nrev = "main"\n' > "$T/r/README.md"; t 1 "comment pins ignored; a branch name is an error"
  setup; printf 'rev = "v9.9.8"\n' > "$T/r/examples/consumer-release/lakefile.toml"; t 1 "consumer-release lakefile pin of a missing tag rejected"
  setup; : > "$T/r/README.md"; printf 'rev = "v9.9.9"\n' > "$T/r/docs/policy.md"; t 1 "a pin elsewhere does not count for README"
  setup; rm "$T/r/docs/policy.md"; t 1 "a missing scanned file is reported"
  setup; printf "rev = 'v9.9.9'\n" > "$T/r/README.md"; t 0 "single-quoted pin of the release tag is recognised"
  setup; printf 'rev\t=  "v9.9.9"\n' > "$T/r/README.md"; t 0 "tab-spaced pin is recognised"
  setup; printf 'require "o" / "oscint" @ git "v9.9.9"\n' > "$T/r/README.md"; t 0 "@ git pin is recognised"
  setup; printf 'rev = "refs/tags/v9.9.9"\n' > "$T/r/README.md"; t 0 "refs/tags/ pin is recognised"
  setup; printf '# rev = "v9.9.8"\nrev = "v9.9.9"\n' > "$T/r/README.md"; t 0 "a comment line naming a missing tag is ignored"
  setup; touch "$NOT_IN_HEAD"; t 1 "a release commit that HEAD (main) does not contain is rejected"
  setup; printf 'rev = "%s"\n' "$C3" > "$T/r/examples/consumer-release/lakefile.toml"; t 1 "a raw commit pin not contained in HEAD is rejected"
  setup; printf 'rev = "%s"\n' "$C1" > "$T/r/examples/consumer-release/lakefile.toml"; t 0 "a raw commit pin contained in HEAD is accepted"
  # the real ancestry predicate, on a real repository: base -> main; base -> side (unmerged); then merge side
  G=$T/g; git init -q -b main "$G" && git -C "$G" -c user.name=t -c user.email=t@t commit -q --allow-empty -m base &&
    git -C "$G" checkout -q -b side && git -C "$G" -c user.name=t -c user.email=t@t commit -q --allow-empty -m side &&
    git -C "$G" checkout -q main && git -C "$G" -c user.name=t -c user.email=t@t commit -q --allow-empty -m main || {
      echo "FAIL self-test: could not build the git fixture"; fails=$((fails+1)); }
  S=$(git -C "$G" rev-parse side)
  if (cd "$G" && in_head "$S"); then echo "FAIL self-test: real in_head accepted an unmerged commit"; fails=$((fails+1))
  else echo "ok   self-test: real in_head rejects a commit on an unmerged branch"; fi
  git -C "$G" -c user.name=t -c user.email=t@t merge -q --no-edit side >/dev/null
  if (cd "$G" && in_head "$S"); then echo "ok   self-test: real in_head accepts it after the merge"
  else echo "FAIL self-test: real in_head rejected a merged commit"; fails=$((fails+1)); fi
  if (cd "$G" && in_head 4444444444444444444444444444444444444444); then
    echo "FAIL self-test: real in_head accepted a nonexistent commit"; fails=$((fails+1))
  else echo "ok   self-test: real in_head rejects a nonexistent commit"; fi
  [ $fails -eq 0 ] && { echo "release-pin self-test: PASS"; exit 0; } || { echo "release-pin self-test: FAIL ($fails)"; exit 1; }
fi

remote=${1:-origin}
cd "$(dirname "$0")/.." || exit 2
listing=$(mktemp); trap 'rm -f "$listing"' EXIT
git ls-remote --tags "$remote" > "$listing" || { echo "ERROR release pin: git ls-remote $remote failed"; exit 2; }
# fetch each recorded release commit into a private ref so `git show` reads the remote's objects
for cf in docs/release-notes/*.commit; do
  [ -f "$cf" ] || continue
  t=$(basename "$cf" .commit)
  git fetch -q --no-tags "$remote" "+refs/tags/$t:refs/release-pin/$t" 2>/dev/null || true
done
show() { git show "$1"; }
ANCESTOR=in_head
if run_checks docs/release-notes "$listing" show; then echo "release-pin: PASS"; exit 0; else echo "release-pin: FAIL"; exit 1; fi
