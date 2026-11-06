#!/usr/bin/env bash
# Negative controls for tools/oscint_check.py, one per check path (lessons 18). Run from examples/consumer after
# `lake build`. Each control must fail with its own message; the positive run must pass. Exit 0 iff all hold.
set -u
CHK=../../tools/oscint_check.py
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fails=0
expect() { # expect <name> <rc> <message regex> -- <checker args...>
  local name=$1 rc=$2 re=$3; shift 4
  out=$(python3 "$CHK" "$@" 2>&1); got=$?
  if [ "$got" -eq "$rc" ] && grep -qE "$re" <<<"$out"; then echo "ok   $name (rc $got)"
  else echo "FAIL $name: rc $got (want $rc), output:"; echo "$out"; fails=$((fails + 1)); fi
}
# a minimal copy of the package metadata that the controls tamper with
mkdir -p "$T/pkg/stamps" "$T/pkg/OscInt"
cp ../../stamps/statements.json "$T/pkg/stamps/"; cp -r ../../OscInt/Statements "$T/pkg/OscInt/"
S=OscInt.Statements.D4LimitStatement
expect "positive: S4.2 checked" 0 "PASS" -- --oscint ../.. --statement $S
expect "wrong pinned hash" 1 "you pinned" -- --oscint ../.. --no-lean --expect-sha256 0000
expect "unknown statement" 1 "not a pinned OscInt statement" -- --oscint ../.. --no-lean --statement OscInt.Statements.Nope
cp -r "$T/pkg" "$T/edited"; echo "-- edited" >> "$T/edited/OscInt/Statements/D4Limit.lean"
expect "edited statement file" 1 "frozen statement file was edited" -- --oscint "$T/edited" --no-lean
swap() { python3 - "$1" "$2" "$3" <<'PY'
import json, sys
p, stmt, thm = sys.argv[1:]; d = json.load(open(p))
for s in d["statements"]:
    if s["name"] == stmt: s["proved_by"] = thm
json.dump(d, open(p, "w"), indent=2)
PY
}
cp -r "$T/pkg" "$T/wrongthm"; swap "$T/wrongthm/stamps/statements.json" $S OscInt.d4Bound
expect "theorem of another statement" 1 "its type is not the constant" -- --oscint "$T/wrongthm" --statement $S
cp -r "$T/pkg" "$T/unproved"; python3 - "$T/unproved/stamps/statements.json" $S <<'PY'
import json, sys
p, stmt = sys.argv[1:]; d = json.load(open(p))
for s in d["statements"]:
    if s["name"] == stmt: s["proved_by"] = None
json.dump(d, open(p, "w"), indent=2)
PY
expect "unproved statement requested" 1 "stated but not proved" -- --oscint "$T/unproved" --no-lean --statement $S
cp -r "$T/pkg" "$T/axiom"; swap "$T/axiom/stamps/statements.json" $S controlTheorem
lake build ConsumerControls >/dev/null 2>&1 || { echo "FAIL could not build ConsumerControls"; exit 1; }
expect "extra axiom" 1 "uses axioms \['controlAxiom'\]" -- --oscint "$T/axiom" --statement $S --import ConsumerControls
echo "test_oscint_check: $fails failure(s)"
[ "$fails" -eq 0 ]
