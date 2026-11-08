#!/usr/bin/env bash
# Negative controls for tools/gen_api.py (lessons 18: each check exercised on the path it exists for).
# Builds a scratch copy of the inputs, plants one defect at a time, and requires --check to FAIL on each,
# and to PASS on the unplanted copy. No network, no Lean.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
fresh() {
  rm -rf "$t/r"; mkdir -p "$t/r/stamps" "$t/r/docs/api" "$t/r/OscInt"
  cp "$here/stamps/statements.json" "$t/r/stamps/"; cp "$here/docs/api/annotations.json" "$t/r/docs/api/"
  cp -r "$here/OscInt/Statements" "$t/r/OscInt/"
  python3 -I "$here/tools/gen_api.py" "$t/r" >/dev/null || { echo "test_gen_api: FAIL: generation failed on clean inputs"; exit 1; }
}
expect_fail() {  # name, then the check must exit non-zero
  if python3 -I "$here/tools/gen_api.py" --check "$t/r" >/dev/null 2>&1; then
    echo "test_gen_api: FAIL: planted defect '$1' was not detected"; exit 1; fi
}
fresh; python3 -I "$here/tools/gen_api.py" --check "$t/r" >/dev/null || { echo "test_gen_api: FAIL: clean copy rejected"; exit 1; }
fresh; echo "-- edited" >> "$t/r/examples/api/Snippets.lean"; expect_fail "Snippets.lean edited by hand"
fresh; sed -i 's/"rate": "m^{-1}"/"rate": "m^{-2}"/' "$t/r/docs/api/annotations.json"; expect_fail "annotation changed, outputs not regenerated"
fresh; python3 -I - "$t/r/docs/api/annotations.json" <<'PY'
import json, sys; p = sys.argv[1]; a = json.load(open(p)); del a['statements']['GD']; json.dump(a, open(p, 'w'))
PY
expect_fail "statement without annotation"
fresh; python3 -I - "$t/r/docs/api/annotations.json" <<'PY'
import json, sys; p = sys.argv[1]; a = json.load(open(p)); a['statements']['S1.1']['snippet'] = 'example : True := trivial'; json.dump(a, open(p, 'w'))
PY
expect_fail "snippet that does not use the proving theorem"
fresh; python3 -I - "$t/r/docs/api/annotations.json" <<'PY'
import json, sys; p = sys.argv[1]; a = json.load(open(p)); a['statements']['S1.1']['see_also'] = ['NOPE']; json.dump(a, open(p, 'w'))
PY
expect_fail "see_also naming an unknown label"
fresh; sed -i 's/^def TorusUnfoldStatement : Prop :=/def TorusUnfoldStatementX : Prop :=/' "$t/r/OscInt/Statements/Global.lean"; expect_fail "statement definition not found in its file"
echo "test_gen_api: PASS (6 planted defects detected, clean copy accepted)"
