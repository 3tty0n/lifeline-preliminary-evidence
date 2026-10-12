#!/bin/bash
# Rerun Evidence A and re-derive the Evidence B numbers. Exits non-zero if any check fails.
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
PY=${PYTHON:-python3}
echo "python: $($PY --version 2>&1)"

echo; echo "=== Evidence A: aggregation core (aggregation-core/)"
# certify.py writes certs/ next to itself, so run it in a scratch copy.
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
cp -r aggregation-core "$TMP/a"
( cd "$TMP/a"
  for s in congruence certify checker; do
    t0=$EPOCHREALTIME
    $PY "$s.py" > "$s.out" 2>&1 || { tail -20 "$s.out"; echo "$s.py FAILED"; exit 1; }
    echo "$s.py: exit 0, $(awk "BEGIN{printf \"%.1f\", $EPOCHREALTIME - $t0}") s"
  done
  grep -E 'Ground truth index|index = (9|79) ' congruence.out
  tail -1 checker.out )
diff -r aggregation-core/certs "$TMP/a/certs" > /dev/null \
  && echo "certify.py output is byte-identical to aggregation-core/certs/" \
  || { echo "certify.py output differs from aggregation-core/certs/"; exit 1; }
$PY aggregation-core/negative_controls.py

echo; echo "=== Evidence B: leave transition (leave-transition/)"
# Every archived file must match its row in SOURCES.txt. "blob" rows are the
# public TensorPyPy commit, "run" rows the archived run data.
bad=0
while read -r mode type blob path; do
  case "$type" in blob|run) ;; *) continue ;; esac
  [ "$(git hash-object "leave-transition/tensorpypy/$path")" = "$blob" ] \
    || { echo "differs from SOURCES.txt: $path"; bad=1; }
done < leave-transition/SOURCES.txt
[ $bad = 0 ] && echo "$(grep -c '^[0-7]* blob ' leave-transition/SOURCES.txt) files match tensorpypy ec9f5fb, $(grep -c '^[0-7]* run ' leave-transition/SOURCES.txt) run files match their recorded hashes"
$PY leave-transition/rederive.py
[ $bad = 0 ]
