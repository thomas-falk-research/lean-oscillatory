#!/usr/bin/env bash
# Fails unless every release tag that the user-facing docs tell people to pin exists in the repository, and the
# release notes for it give the SHA-256 that `stamps/statements.json` and `tools/oscint_check.py` have AT THAT TAG.
# Files scanned: README.md, docs/policy.md, examples/consumer/lakefile.toml (lines `rev = "vX.Y.Z"` or `@ "vX.Y.Z"`).
#
# Usage: tools/check_release_pin.sh [REMOTE]     (REMOTE defaults to `origin`; CI passes the repository URL)
#        tools/check_release_pin.sh --self-test  (negative controls; no network)
# Exit: 0 every pinned tag exists and matches its release notes; 1 a check failed; 2 usage or environment error.
set -euo pipefail

scan() { # prints each distinct pinned tag in the files given
  grep -hoE '(rev *= *|@ *)"v[0-9]+\.[0-9]+\.[0-9]+"' "$@" 2>/dev/null | grep -oE 'v[0-9]+\.[0-9]+\.[0-9]+' | sort -u
}

# check_tag <tag> <tags-listing-file> <notes-dir> <show-cmd...>: show-cmd prints a file at the tag (`git show`)
check_tag() {
  local tag=$1 listing=$2 notes=$3; shift 3
  if ! grep -qE "refs/tags/${tag//./\\.}(\^\{\})?$" "$listing"; then
    echo "FAIL release pin: the docs tell users to pin $tag, but tag $tag does not exist in the repository."
    echo "     Fix: the owner publishes release $tag (steps in $notes/$tag.md), or the docs pin an existing tag."
    return 1
  fi
  local nf="$notes/$tag.md"
  if [ ! -f "$nf" ]; then
    echo "FAIL release pin: tag $tag exists but $nf (its release notes, with the SHA-256 pins) is missing."
    return 1
  fi
  local f h rc=0
  for f in stamps/statements.json tools/oscint_check.py; do
    if ! h=$("$@" "$tag:$f" | sha256sum | cut -d' ' -f1); then
      echo "FAIL release pin: could not read $f at tag $tag"; rc=1; continue
    fi
    if ! grep -qE "^\| \`$f\` \| \`$h\` \|" "$nf"; then
      echo "FAIL release pin: $f at tag $tag has SHA-256 $h, which $nf does not give (table row \"| \`$f\` | \`<sha256>\` |\")."
      rc=1
    fi
  done
  [ $rc -eq 0 ] && echo "ok   release pin $tag: tag exists; $nf gives the SHA-256 of both pinned files at the tag"
  return $rc
}

if [ "${1:-}" = "--self-test" ]; then
  T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
  mkdir -p "$T/notes"
  fake_show() { case "$1" in *statements.json) printf 'S';; *oscint_check.py) printf 'C';; *) return 1;; esac; }
  hs=$(printf 'S' | sha256sum | cut -d' ' -f1); hc=$(printf 'C' | sha256sum | cut -d' ' -f1)
  printf 'abc\trefs/tags/v9.9.9\n' > "$T/tags"
  fails=0
  t() { local want=$1 name=$2; shift 2; if out=$("$@" 2>&1); then got=0; else got=1; fi
        if [ "$got" = "$want" ]; then echo "ok   self-test: $name"; else echo "FAIL self-test: $name (rc $got, want $want): $out"; fails=$((fails+1)); fi; }
  t 1 "missing tag rejected" check_tag v9.9.8 "$T/tags" "$T/notes" fake_show
  t 1 "missing release notes rejected" check_tag v9.9.9 "$T/tags" "$T/notes" fake_show
  printf '| `stamps/statements.json` | `%s` |\n| `tools/oscint_check.py` | `%s` |\n' "$hs" "0000" > "$T/notes/v9.9.9.md"
  t 1 "wrong checker hash rejected" check_tag v9.9.9 "$T/tags" "$T/notes" fake_show
  printf '| `stamps/statements.json` | `%s` |\n| `tools/oscint_check.py` | `%s` |\n' "$hs" "$hc" > "$T/notes/v9.9.9.md"
  t 0 "correct pin accepted" check_tag v9.9.9 "$T/tags" "$T/notes" fake_show
  printf 'abc\trefs/tags/v9.9.90\n' > "$T/tags"
  t 1 "tag prefix (v9.9.90) does not satisfy v9.9.9" check_tag v9.9.9 "$T/tags" "$T/notes" fake_show
  printf 'rev = "v1.2.3"\n# x @ "v4.5.6"\nrev = "abc123"\n' > "$T/scan.toml"
  [ "$(scan "$T/scan.toml" | tr '\n' ' ')" = "v1.2.3 v4.5.6 " ] && echo "ok   self-test: scan finds tag pins only" \
    || { echo "FAIL self-test: scan"; fails=$((fails+1)); }
  [ $fails -eq 0 ] && echo "release-pin self-test: PASS" || { echo "release-pin self-test: FAIL ($fails)"; exit 1; }
  exit 0
fi

remote=${1:-origin}
cd "$(dirname "$0")/.."
tags=$(scan README.md docs/policy.md examples/consumer/lakefile.toml)
[ -n "$tags" ] || { echo "FAIL release pin: no pinned tag found in README.md (expected a line rev = \"vX.Y.Z\")"; exit 1; }
listing=$(mktemp); trap 'rm -f "$listing"' EXIT
git ls-remote --tags "$remote" > "$listing" || { echo "ERROR release pin: git ls-remote $remote failed"; exit 2; }
rc=0
for tag in $tags; do
  git fetch -q --depth 1 "$remote" "refs/tags/$tag:refs/tags/$tag" 2>/dev/null || true
  check_tag "$tag" "$listing" docs/release-notes git show || rc=1
done
[ $rc -eq 0 ] && echo "release-pin: PASS" || echo "release-pin: FAIL"
exit $rc
