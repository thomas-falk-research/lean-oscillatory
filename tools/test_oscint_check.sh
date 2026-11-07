#!/usr/bin/env bash
# Positive run and negative controls for tools/oscint_check.py: one control per check path, each must be rejected
# with its own message (lessons 18). Run from examples/consumer after `lake build`. Exit 0 iff all hold.
# The full positive run and the kernel and commitment controls take about half an hour.
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
edit() { python3 - "$@" <<'PY'
import json, sys
p, stmt, key, val = sys.argv[1:]; d = json.load(open(p))
for s in d["statements"]:
    if s["name"] == stmt: s[key] = None if val == "null" else val
json.dump(d, open(p, "w"), indent=2)
PY
}
# a minimal copy of the package metadata that the controls tamper with
mkdir -p "$T/pkg/stamps" "$T/pkg/OscInt"
cp ../../stamps/statements.json "$T/pkg/stamps/"; cp -r ../../OscInt/Statements "$T/pkg/OscInt/"
copy() { rm -rf "$T/$1"; cp -r "$T/pkg" "$T/$1"; echo "$T/$1"; }
S=OscInt.Statements.D4LimitStatement
H=$(sha256sum ../../stamps/statements.json | cut -d' ' -f1)
lake build ConsumerControls ConsumerKernelControl >/dev/null 2>&1 || { echo "FAIL could not build the control libraries"; exit 1; }

expect "positive: full check of S4.2" 0 "^oscint-check: PASS" -- --oscint ../.. --statement $S --expect-sha256 "$H"
expect "partial run is not PASS" 0 "^oscint-check: PARTIAL" -- --oscint ../.. --statement $S --fast
# files and metadata
expect "wrong pinned hash" 1 "you pinned" -- --oscint ../.. --no-lean --expect-sha256 0000
expect "unknown statement" 1 "not a pinned OscInt statement" -- --oscint ../.. --no-lean --statement OscInt.Statements.Nope
P=$(copy edited); echo "-- edited" >> "$P/OscInt/Statements/D4Limit.lean"
expect "edited statement file" 1 "frozen statement file was edited" -- --oscint "$P" --no-lean
P=$(copy extra); cp "$P/OscInt/Statements/D4.lean" "$P/OscInt/Statements/Extra.lean"
expect "unstamped statement file" 1 "not in stamps/statements.json" -- --oscint "$P" --no-lean
P=$(copy unproved); edit "$P/stamps/statements.json" $S proved_by null
expect "unproved statement requested" 1 "stated but not proved" -- --oscint "$P" --no-lean --statement $S
# toolchain and Mathlib of the consumer
mkdir -p "$T/proj1" "$T/proj2"; cp lake-manifest.json "$T/proj1/"; echo "leanprover/lean4:v4.34.0" > "$T/proj1/lean-toolchain"
cp lean-toolchain "$T/proj2/"; sed 's/"rev": "56a005855ea17e0b0958f73ec801ae140b0a1679"/"rev": "0000000000000000000000000000000000000000"/' lake-manifest.json > "$T/proj2/lake-manifest.json"
expect "other toolchain" 1 "your lean-toolchain is" -- --project "$T/proj1" --oscint ../.. --no-lean
expect "other Mathlib" 1 "your Mathlib revision is" -- --project "$T/proj2" --oscint ../.. --no-lean
# Lean checks (each control skips the slow paths it does not exercise)
P=$(copy wrongthm); edit "$P/stamps/statements.json" $S proved_by OscInt.d4Bound
expect "theorem of another statement" 1 "its type is not the constant" -- --oscint "$P" --statement $S --fast
P=$(copy defeq); edit "$P/stamps/statements.json" $S proved_by controlDefeq
expect "defeq-only type" 1 "its type is not the constant" -- --oscint "$P" --statement $S --fast --import ConsumerControls
P=$(copy module); edit "$P/stamps/statements.json" $S file OscInt/Statements/D4.lean
expect "statement from another module" 1 "is declared in module OscInt.Statements.D4Limit, not in OscInt.Statements.D4" -- --oscint "$P" --statement $S --fast
P=$(copy axiom); edit "$P/stamps/statements.json" $S proved_by controlTheorem
expect "extra axiom" 1 "uses axioms \['controlAxiom'\]" -- --oscint "$P" --statement $S --fast --import ConsumerControls
P=$(copy kernel); edit "$P/stamps/statements.json" $S proved_by controlUnchecked
expect "kernel-unchecked theorem" 1 "kernel replay rejected module ConsumerKernelControl" -- --oscint "$P" --statement $S --no-commitments --import ConsumerKernelControl
P=$(copy commit); edit "$P/stamps/statements.json" $S commitment 0000000000000000000000000000000000000000000000000000000000000000
expect "changed commitment" 1 "recomputed commitment .* stamped 0000" -- --oscint "$P" --statement $S --no-kernel
echo "test_oscint_check: $fails failure(s)"
[ "$fails" -eq 0 ]
