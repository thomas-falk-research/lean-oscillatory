#!/usr/bin/env bash
# Entry-point check: `import OscInt.API` (the documented entry point, README) must expose every statement constant
# and every proving theorem listed in stamps/statements.json. Generates a Lean file and elaborates it.
# Usage: tools/check_entry_point.sh            (from anywhere; needs a built library)
#        tools/check_entry_point.sh --self-test (a name that does not exist must be reported)
# Exit 0 pass, 1 a name is missing, 2 environment error.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
names=$(python3 -I -c '
import json
d = json.load(open("stamps/statements.json"))
for s in d["statements"]:
    print(s["name"])
    if s.get("proved_by"): print(s["proved_by"])
') || { echo "ERROR entry-point: cannot read stamps/statements.json"; exit 2; }
# No module except the root may have submodules: `leanchecker M` replays every module whose name starts with `M.`,
# each in a parallel task with its own environment (LeanChecker.lean), which ran out of memory (lessons 30).
mods=$(find OscInt -name '*.lean' | sed 's#\.lean$##; s#/#.#g' | sort)
nested=$(for m in $mods; do grep -q "^$m\." <<<"$mods" && echo "$m"; done)
if [ "${1:-}" = "--self-test" ]; then
  fake=$'OscInt.A\nOscInt.A.B\nOscInt.C'
  got=$(for m in $fake; do grep -q "^$m\." <<<"$fake" && echo "$m"; done)
  [ "$got" = "OscInt.A" ] && echo "ok   self-test: nested-module detector flags OscInt.A (has OscInt.A.B) and nothing else" \
    || { echo "FAIL self-test: nested-module detector returned '$got'"; exit 1; }
fi
if [ "${1:-}" != "--self-test" ] && [ -n "$nested" ]; then
  echo "FAIL entry-point: these modules have submodules (move the submodules elsewhere, e.g. OscInt/Front/): $nested"
  exit 1
fi
[ "${1:-}" = "--self-test" ] && names="$names
OscInt.API.noSuchTheoremForTheSelfTest"
{ echo "import OscInt.API"; for n in $names; do echo "#check @$n"; done; } > "$T/Entry.lean"
out=$(lake env lean "$T/Entry.lean" 2>&1); rc=$?
missing=$(grep -oE "Unknown (constant|identifier) \`[^\`]+\`" <<<"$out" | sort -u)
if [ "${1:-}" = "--self-test" ]; then
  if grep -q noSuchTheoremForTheSelfTest <<<"$missing" && [ "$(grep -c . <<<"$missing")" -eq 1 ]; then
    echo "entry-point self-test: PASS (the planted name is reported, nothing else)"; exit 0
  fi
  echo "entry-point self-test: FAIL"; echo "$out" | head -20; exit 1
fi
if [ $rc -ne 0 ] || [ -n "$missing" ]; then
  echo "FAIL entry-point: \`import OscInt.API\` does not expose:"; echo "$missing"; [ -n "$missing" ] || echo "$out" | head -20
  echo "     Fix: import the module that declares it from OscInt/API.lean."
  exit 1
fi
echo "entry-point: PASS ($(grep -c . <<<"$names") names from stamps/statements.json, all visible under import OscInt.API)"
