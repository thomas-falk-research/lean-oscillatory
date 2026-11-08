#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0

# Release preflight: is the checked-out commit ready to be released as vVERSION?
# Used by .github/workflows/release.yml (before the replay) and post-release.yml (on the tagged commit), and locally:
#   tools/release_preflight.sh 0.4.0          # exit 0 ready; 1 not ready (each problem on its own line)
#   tools/release_preflight.sh --self-test    # negative controls on a scratch copy (no network)
# Checks: the version is X.Y.Z; lakefile.toml, CITATION.cff, .zenodo.json and codemeta.json carry it; CHANGELOG.md has a
# `## vX.Y.Z` section; docs/release-notes/vX.Y.Z.md exists, has exactly one table row each for stamps/statements.json
# and tools/oscint_check.py with their SHA-256 in this tree, and every `--expect-sha256` in it is the statements.json
# hash. It does not check tags, CI or the network (the workflows do).
set -uo pipefail

check() {
  local root=$1 v=$2 bad=0 tag notes f h rows n sj e
  say() { echo "preflight: $*"; bad=1; }
  echo "$v" | grep -qxE '[0-9]+\.[0-9]+\.[0-9]+' || { say "version '$v' is not X.Y.Z"; return 1; }
  tag="v$v"; notes="$root/docs/release-notes/$tag.md"
  grep -qxF "version = \"$v\"" "$root/lakefile.toml" || say "lakefile.toml does not say: version = \"$v\""
  grep -qxF "version: \"$v\"" "$root/CITATION.cff" || say "CITATION.cff does not say: version: \"$v\""
  python3 -I -c 'import json,sys; sys.exit(json.load(open(sys.argv[1])).get("version") != sys.argv[2])' \
    "$root/.zenodo.json" "$v" || say ".zenodo.json does not say: \"version\": \"$v\""
  python3 -I -c 'import json,sys; sys.exit(json.load(open(sys.argv[1])).get("version") != sys.argv[2])' \
    "$root/codemeta.json" "$v" || say "codemeta.json does not say: \"version\": \"$v\""
  grep -qE "^## $tag( |$)" "$root/CHANGELOG.md" || say "CHANGELOG.md has no '## $tag' section"
  if [ ! -f "$notes" ]; then say "docs/release-notes/$tag.md is missing"; return 1; fi
  for f in stamps/statements.json tools/oscint_check.py; do
    h=$(sha256sum "$root/$f" | cut -d' ' -f1)
    rows=$(grep -F "| \`$f\` |" "$notes" || true); n=$(grep -c . <<<"$rows" || true); [ -n "$rows" ] || n=0
    if [ "$n" -ne 1 ]; then say "docs/release-notes/$tag.md has $n rows for $f; it needs exactly: | \`$f\` | \`$h\` |"
    elif ! grep -qF "| \`$h\` |" <<<"$rows"; then say "docs/release-notes/$tag.md: the row for $f must be: | \`$f\` | \`$h\` |"; fi
  done
  sj=$(sha256sum "$root/stamps/statements.json" | cut -d' ' -f1)
  while read -r e; do
    [ -z "$e" ] || [ "$e" = "$sj" ] || say "docs/release-notes/$tag.md uses --expect-sha256 $e; it must be $sj"
  done < <(grep -oE -- '--expect-sha256[[:space:]]+[0-9a-f]+' "$notes" | awk '{print $2}')
  [ "$bad" -eq 0 ] && echo "preflight: $tag ready (versions, CHANGELOG, notes and pins agree with this tree)"
  return "$bad"
}

self_test() {
  local here t v=9.9.9 rc=0
  here=$(cd "$(dirname "$0")/.." && pwd); t=$(mktemp -d); trap 'rm -rf "$t"' RETURN
  mk() {
    rm -rf "$t/r"; mkdir -p "$t/r/stamps" "$t/r/tools" "$t/r/docs/release-notes"
    cp "$here/stamps/statements.json" "$t/r/stamps/"; cp "$here/tools/oscint_check.py" "$t/r/tools/"
    printf 'name = "oscint"\nversion = "%s"\n' "$v" > "$t/r/lakefile.toml"
    printf 'version: "%s"\n' "$v" > "$t/r/CITATION.cff"
    printf '{"version": "%s"}\n' "$v" > "$t/r/.zenodo.json"
    printf '{"version": "%s"}\n' "$v" > "$t/r/codemeta.json"
    printf '# Changelog\n\n## v%s — test\n' "$v" > "$t/r/CHANGELOG.md"
    local a b; a=$(sha256sum "$t/r/stamps/statements.json" | cut -d' ' -f1); b=$(sha256sum "$t/r/tools/oscint_check.py" | cut -d' ' -f1)
    # shellcheck disable=SC2016  # the backticks are Markdown, not command substitution
    printf '| `stamps/statements.json` | `%s` |\n| `tools/oscint_check.py` | `%s` |\n--expect-sha256 %s\n' "$a" "$b" "$a" \
      > "$t/r/docs/release-notes/v$v.md"
  }
  want() {  # name, expected exit status
    local got; check "$t/r" "$v" >/dev/null 2>&1; got=$?
    if [ "$got" -ne "$2" ]; then echo "release_preflight self-test: FAIL: $1 (exit $got, want $2)"; rc=1; fi
  }
  mk; want "clean copy" 0
  mk; sed -i 's/9.9.9/9.9.8/' "$t/r/lakefile.toml"; want "lakefile version" 1
  mk; sed -i 's/9.9.9/9.9.8/' "$t/r/CITATION.cff"; want "CITATION version" 1
  mk; echo '{"version": "9.9.8"}' > "$t/r/.zenodo.json"; want "zenodo version" 1
  mk; echo '{"version": "9.9.8"}' > "$t/r/codemeta.json"; want "codemeta version" 1
  mk; echo '# Changelog' > "$t/r/CHANGELOG.md"; want "CHANGELOG section" 1
  mk; echo x >> "$t/r/stamps/statements.json"; want "statements.json pin" 1
  mk; echo x >> "$t/r/tools/oscint_check.py"; want "checker pin" 1
  mk; echo '--expect-sha256 0000' >> "$t/r/docs/release-notes/v$v.md"; want "expect-sha256" 1
  mk; local row; row=$(head -1 "$t/r/docs/release-notes/v$v.md"); echo "$row" >> "$t/r/docs/release-notes/v$v.md"
  want "duplicate row" 1
  mk; rm "$t/r/docs/release-notes/v$v.md"; want "missing notes" 1
  [ "$rc" -eq 0 ] && echo "release_preflight self-test: PASS (10 planted defects detected, clean copy accepted)"
  return "$rc"
}

case "${1:-}" in
  --self-test) self_test ;;
  ""|-h|--help) sed -n '2,10p' "$0"; exit 2 ;;
  *) check "$(cd "$(dirname "$0")/.." && pwd)" "$1" ;;
esac
