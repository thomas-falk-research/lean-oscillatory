#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0

# Release preflight: is the checked-out commit ready to be released as vVERSION?
# Used by .github/workflows/release-candidate.yml (before the replay) and post-release.yml (on the tagged commit), and
# locally:
#   tools/release_preflight.sh 0.6.0          # exit 0 ready; 1 not ready (each problem on its own line)
#   tools/release_preflight.sh --self-test    # negative controls on a scratch copy (no network)
# Checks:
# - the version is X.Y.Z; lakefile.toml, CITATION.cff, .zenodo.json and codemeta.json carry it; CHANGELOG.md has a
#   `## vX.Y.Z` section; docs/release-notes/vX.Y.Z.md exists, has exactly one table row each for stamps/statements.json
#   and tools/oscint_check.py with their SHA-256 in this tree, and every `--expect-sha256` in it is the statements.json
#   hash;
# - the dates agree: CITATION.cff `date-released`, codemeta.json `datePublished` and the CHANGELOG heading
#   `## vX.Y.Z — YYYY-MM-DD`;
# - every `rev = "v…"` in the release notes is this release's tag;
# - every `proved_by` theorem of stamps/statements.json is a `theorem_names` entry of some comparator*.json, so no
#   proved statement can be skipped by the comparator (verify.yml skips a configuration with nothing to check);
# - against the previous release (the greatest tag vA.B.C below vX.Y.Z; `git fetch --tags` if none is found): the
#   version is greater; the release class matches docs/policy.md (a patch leaves stamps/statements.json byte-identical;
#   from 1.0.0 a minor only adds entries or sets a `proved_by` that was null); every added, removed or changed entry's
#   label is named in the
#   notes' `## Statement changes` section and in a `### Statement changes…` subsection of the CHANGELOG section.
# It does not check CI or the network (the workflows and tools/publish_release.sh do).
set -uo pipefail

# policy ROOT VERSION PREV_VERSION PREV_STATEMENTS: the checks that compare files with each other and with the previous
# release. Prints one "preflight: …" line per problem and exits 1 if there is any.
policy() {
  python3 -I - "$@" <<'PY'
import glob, json, os, re, sys
root, v, pv, psj = sys.argv[1:5]
tag = "v" + v
bad = []
def say(m): bad.append(m)
def read(p):
    with open(os.path.join(root, p), encoding="utf-8") as f: return f.read()
def ver(s): return tuple(int(x) for x in s.split("."))

notes = read(f"docs/release-notes/{tag}.md")
changelog = read("CHANGELOG.md")
m = re.search(rf"^## {re.escape(tag)}(?: [^\n]*)?$(.*?)(?=^## v|\Z)", changelog, re.M | re.S)
section = m.group(1) if m else ""

# dates
dates = {}
m = re.search(r'^date-released:\s*"?(\d{4}-\d{2}-\d{2})"?\s*$', read("CITATION.cff"), re.M)
dates["CITATION.cff date-released"] = m.group(1) if m else None
try:
    dates["codemeta.json datePublished"] = json.loads(read("codemeta.json")).get("datePublished")
except ValueError:
    dates["codemeta.json datePublished"] = None
m = re.search(rf"^## {re.escape(tag)} — (\d{{4}}-\d{{2}}-\d{{2}})\s*$", changelog, re.M)
dates[f"CHANGELOG `## {tag} — <date>`"] = m.group(1) if m else None
for k, d in dates.items():
    if not d: say(f"no date found for {k}")
if all(dates.values()) and len(set(dates.values())) != 1:
    say("the dates disagree: " + ", ".join(f"{k} {d}" for k, d in dates.items()))

# downstream snippets in the notes
for r in re.findall(r"""rev\s*=\s*["'](v[^"']*)["']""", notes):
    if r != tag: say(f"docs/release-notes/{tag}.md pins rev = \"{r}\"; it must be \"{tag}\"")

# statements
try:
    cur = json.loads(read("stamps/statements.json"))
except ValueError as e:
    print(f"preflight: stamps/statements.json is not JSON ({e})"); sys.exit(1)
proved = {s["proved_by"] for s in cur["statements"] if s.get("proved_by")}
covered = set()
for p in sorted(glob.glob(os.path.join(root, "comparator*.json"))):
    with open(p, encoding="utf-8") as f: covered |= set(json.load(f).get("theorem_names", []))
for n in sorted(proved - covered):
    say(f"proved_by {n} is in no comparator*.json theorem_names, so the comparator would not check it")

if not pv:
    say(f"no release tag below {tag} found to compare with (git fetch --tags)")
else:
    a, b = ver(v), ver(pv)
    if a <= b:
        say(f"{tag} is not greater than the previous release v{pv}")
    else:
        kind = "major" if a[0] > b[0] else "minor" if a[1] > b[1] else "patch"
        with open(psj, "rb") as f: pbytes = f.read()
        with open(os.path.join(root, "stamps/statements.json"), "rb") as f: cbytes = f.read()
        prev = json.loads(pbytes)
        pe = {s["name"]: s for s in prev["statements"]}
        ce = {s["name"]: s for s in cur["statements"]}
        changed = sorted(n for n in pe.keys() | ce.keys() if pe.get(n) != ce.get(n))
        labels = sorted({(ce.get(n) or pe[n])["label"] for n in changed})
        if kind == "patch" and pbytes != cbytes:
            say(f"{tag} is a patch release after v{pv}, but stamps/statements.json differs from v{pv}'s; a patch "
                "changes no statement entry or statement file (docs/policy.md): make it a minor release")
        elif kind == "minor" and a[0] >= 1:
            # from 1.0.0 a minor adds entries; an existing one may change only by proved_by going from null to a name
            def allowed(n):
                if n not in pe: return True
                if n not in ce: return False
                p, c = dict(pe[n]), dict(ce[n])
                return p.pop("proved_by", None) is None and c.pop("proved_by", None) is not None and p == c
            bad_entries = sorted({pe[n]["label"] for n in changed if not allowed(n)})
            if bad_entries:
                say(f"{tag} is a minor release after v{pv} but changes or removes entries {bad_entries} beyond "
                    "setting a null proved_by; from 1.0.0 that needs a major release (docs/policy.md)")
        ns = re.search(r"^## Statement changes[ \t]*$(.*?)(?=^## |\Z)", notes, re.M | re.S)
        nsec = ns.group(1) if ns else ""
        csec = "".join(re.findall(r"^### Statement changes[^\n]*$(.*?)(?=^##|\Z)", section, re.M | re.S))
        def named(label, text):
            # a label ends where no label character follows: LS-D is not named by LS-D′, LS-D' or LS-D-V,
            # S1 not by S1.k, S2.1 not by FE-S2.1
            return re.search(r"(?<![\w′″'.\-])" + re.escape(label) + r"(?![\w′″'\-]|\.\w)", text) is not None
        for lab in labels:
            if not named(lab, nsec):
                say(f"statement {lab} changed since v{pv} but is not named in the `## Statement changes` section "
                    f"of docs/release-notes/{tag}.md")
            if not named(lab, csec):
                say(f"statement {lab} changed since v{pv} but is not named in a `### Statement changes` "
                    f"subsection of the CHANGELOG section `## {tag}`")
        if not bad:
            print(f"preflight: {tag} is a {kind} release after v{pv}; statement entries changed: "
                  + (", ".join(labels) if labels else "none"))
for m in bad: print(f"preflight: {m}")
sys.exit(1 if bad else 0)
PY
}

# check ROOT VERSION PREV_VERSION PREV_STATEMENTS
check() {
  local root=$1 v=$2 pv=$3 psj=$4 bad=0 tag notes f h rows n sj e
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
  policy "$root" "$v" "$pv" "$psj" || bad=1
  [ "$bad" -eq 0 ] && echo "preflight: $tag ready (versions, dates, CHANGELOG, notes, pins and statement changes agree with this tree and v$pv)"
  return "$bad"
}

# the greatest release tag vA.B.C strictly below vVERSION in ROOT's repository, without the v (empty if none)
previous() {
  git -C "$1" tag -l 'v*' | python3 -I -c '
import re, sys
cur = tuple(int(x) for x in sys.argv[1].split("."))
vs = [tuple(int(x) for x in t[1:].split(".")) for t in sys.stdin.read().split() if re.fullmatch(r"v\d+\.\d+\.\d+", t)]
below = sorted(x for x in vs if x < cur)
print(".".join(map(str, below[-1])) if below else "")' "$2"
}

main_check() {
  local root v pv psj rc
  root=$(cd "$(dirname "$0")/.." && pwd); v=$1
  echo "$v" | grep -qxE '[0-9]+\.[0-9]+\.[0-9]+' || { echo "preflight: version '$v' is not X.Y.Z"; return 1; }
  pv=$(previous "$root" "$v"); psj=$(mktemp)
  if [ -n "$pv" ] && ! git -C "$root" show "v$pv:stamps/statements.json" > "$psj" 2>/dev/null; then
    echo "preflight: v$pv has no stamps/statements.json to compare with"; rm -f "$psj"; return 1
  fi
  check "$root" "$v" "$pv" "$psj"; rc=$?
  rm -f "$psj"; return "$rc"
}

self_test() {
  local here t v=0.9.9 pv=0.9.8 rc=0 label
  here=$(cd "$(dirname "$0")/.." && pwd); t=$(mktemp -d); trap 'rm -rf "$t"' RETURN
  label=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["statements"][0]["label"])' \
    "$here/stamps/statements.json")
  mk() {
    rm -rf "$t/r"; mkdir -p "$t/r/stamps" "$t/r/tools" "$t/r/docs/release-notes"
    cp "$here/stamps/statements.json" "$t/r/stamps/"; cp "$here/tools/oscint_check.py" "$t/r/tools/"
    cp "$here"/comparator*.json "$t/r/"
    cp "$here/stamps/statements.json" "$t/prev.json"
    printf 'name = "oscint"\nversion = "%s"\n' "$v" > "$t/r/lakefile.toml"
    printf 'version: "%s"\ndate-released: "2026-01-02"\n' "$v" > "$t/r/CITATION.cff"
    printf '{"version": "%s"}\n' "$v" > "$t/r/.zenodo.json"
    printf '{"version": "%s", "datePublished": "2026-01-02"}\n' "$v" > "$t/r/codemeta.json"
    printf '# Changelog\n\n## v%s — 2026-01-02\n\n### Statement changes\n\nNone.\n\n## v%s — 2026-01-01\n' \
      "$v" "$pv" > "$t/r/CHANGELOG.md"
    local a b; a=$(sha256sum "$t/r/stamps/statements.json" | cut -d' ' -f1); b=$(sha256sum "$t/r/tools/oscint_check.py" | cut -d' ' -f1)
    # shellcheck disable=SC2016  # the backticks are Markdown, not command substitution
    printf '| `stamps/statements.json` | `%s` |\n| `tools/oscint_check.py` | `%s` |\n--expect-sha256 %s\nrev = "v%s"\n\n## Statement changes\n\nNone.\n' \
      "$a" "$b" "$a" "$v" > "$t/r/docs/release-notes/v$v.md"
  }
  want() {  # name, expected exit status[, previous version]
    local got; check "$t/r" "$v" "${3-$pv}" "$t/prev.json" >/dev/null 2>&1; got=$?
    if [ "$got" -ne "$2" ]; then echo "release_preflight self-test: FAIL: $1 (exit $got, want $2)"; rc=1; fi
  }
  # a previous release in which the first entry's FIELD (default proved_by) was null
  prev_changed() {
    python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); d["statements"][0][sys.argv[2]]=None
json.dump(d, open(sys.argv[1], "w"))' "$t/prev.json" "${1:-proved_by}"
  }
  # the change named in the notes' and the CHANGELOG's statement-change sections (as NAME)
  name_it() {
    printf '\n%s\n' "$1" >> "$t/r/docs/release-notes/v$v.md"
    sed -i "s/^None\.\$/$1 changed./" "$t/r/CHANGELOG.md"
  }
  mk; want "clean copy" 0
  mk; sed -i "s/$v/0.9.7/" "$t/r/lakefile.toml"; want "lakefile version" 1
  mk; sed -i "s/^version: \"$v\"/version: \"0.9.7\"/" "$t/r/CITATION.cff"; want "CITATION version" 1
  mk; echo '{"version": "0.9.7"}' > "$t/r/.zenodo.json"; want "zenodo version" 1
  mk; echo '{"version": "0.9.7", "datePublished": "2026-01-02"}' > "$t/r/codemeta.json"; want "codemeta version" 1
  mk; echo '# Changelog' > "$t/r/CHANGELOG.md"; want "CHANGELOG section" 1
  mk; echo x >> "$t/r/stamps/statements.json"; want "statements.json pin" 1
  mk; echo x >> "$t/r/tools/oscint_check.py"; want "checker pin" 1
  mk; echo '--expect-sha256 0000' >> "$t/r/docs/release-notes/v$v.md"; want "expect-sha256" 1
  mk; local row; row=$(head -1 "$t/r/docs/release-notes/v$v.md"); echo "$row" >> "$t/r/docs/release-notes/v$v.md"
  want "duplicate row" 1
  mk; rm "$t/r/docs/release-notes/v$v.md"; want "missing notes" 1
  mk; sed -i 's/2026-01-02/2026-01-03/' "$t/r/CITATION.cff"; want "dates disagree" 1
  mk; sed -i "s/^## v$v — 2026-01-02/## v$v/" "$t/r/CHANGELOG.md"; want "CHANGELOG date missing" 1
  mk; echo "rev = \"v$pv\"" >> "$t/r/docs/release-notes/v$v.md"; want "stale rev in notes" 1
  mk; rm "$t/r"/comparator*.json; want "proved_by not covered by a comparator" 1
  mk; want "no previous release" 1 ""
  mk; want "version not greater than the previous" 1 "$v"
  mk; prev_changed; want "patch release with changed statements" 1
  mk; prev_changed; want "minor release, changed statement not named" 1 0.8.0
  mk; prev_changed; printf '\n%s\n' "$label" >> "$t/r/docs/release-notes/v$v.md"; want "minor, named in notes only" 1 0.8.0
  mk; prev_changed; name_it "$label"; want "minor before 1.0, named in notes and CHANGELOG" 0 0.8.0
  mk; prev_changed; name_it "${label}′x"; want "minor, only a longer label named" 1 0.8.0
  mk; prev_changed; printf '\n%s\n' "$label" >> "$t/r/docs/release-notes/v$v.md"
  printf '\n### Statement changes\n\n%s changed.\n' "$label" >> "$t/r/CHANGELOG.md"
  want "minor, named only in an older CHANGELOG section" 1 0.8.0
  # label boundaries: each text names a longer or different label only
  local other
  for other in "FE-$label" "$label.k" "$label-V" "$label'" "$label$(printf '\xe2\x80\xb3')"; do
    mk; prev_changed; name_it "$other"; want "minor, only '$other' named" 1 0.8.0
  done
  # the notes' statement-changes section ends at the next `## ` heading
  mk; prev_changed; printf '\n## Evidence\n\n%s\n' "$label" >> "$t/r/docs/release-notes/v$v.md"
  sed -i "s/^None\.\$/$label changed./" "$t/r/CHANGELOG.md"; want "minor, named only after the notes' section" 1 0.8.0
  # from 1.0.0 a minor may set a null proved_by, and nothing else
  v=1.9.9; mk; prev_changed; name_it "$label"; want "minor from 1.0 setting a null proved_by" 0 1.8.0
  mk; prev_changed commitment; name_it "$label"; want "minor from 1.0 changing a commitment" 1 1.8.0
  mk; prev_changed; name_it "$label"; want "major (0.9.0 to 1.9.9) changing an entry" 0 0.9.0; v=0.9.9
  # previous(): the greatest vA.B.C below, numerically, ignoring other tags
  git -C "$t" init -q tags && git -C "$t/tags" -c user.name=t -c user.email=t@t commit -q --allow-empty -m t
  local x; for x in v0.9.0 v0.10.1 v1.0.0-rc1 vfoo v2.0.0; do git -C "$t/tags" tag "$x"; done
  [ "$(previous "$t/tags" 1.0.0)" = 0.10.1 ] || { echo "release_preflight self-test: FAIL: previous below 1.0.0"; rc=1; }
  [ "$(previous "$t/tags" 0.10.0)" = 0.9.0 ] || { echo "release_preflight self-test: FAIL: previous below 0.10.0"; rc=1; }
  [ -z "$(previous "$t/tags" 0.9.0)" ] || { echo "release_preflight self-test: FAIL: nothing below 0.9.0"; rc=1; }
  [ "$rc" -eq 0 ] && echo "release_preflight self-test: PASS (28 planted defects detected, 4 clean copies accepted, 3 previous-tag checks)"
  return "$rc"
}

case "${1:-}" in
  --self-test) self_test ;;
  ""|-h|--help) sed -n '2,25p' "$0"; exit 2 ;;
  *) main_check "$1" ;;
esac
