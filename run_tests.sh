#!/bin/sh
# run_tests.sh -- reproduce every session of the manuscript and the regression
# tests, compare with the stored outputs, and run the independent checks.
# Requires Singular (tested with 4.3.2) and, for the checks, python3.
cd "$(dirname "$0")" || exit 1
status=0
check () {   # $1 folder, $2 script, $3 expected output
  ( cd "$1" && Singular -q "$2" > "$3.new" 2>&1 )
  if diff -b -q "$1/$3" "$1/$3.new" > /dev/null; then
    echo "[ OK ] $1/$2 reproduces $1/$3"; rm -f "$1/$3.new"
  else
    echo "[DIFF] $1/$2 differs from $1/$3 (see $1/$3.new)"; status=1
  fi
}
check examples examples.sing examples_output.txt
check examples integer_groebner.sing integer_groebner_output.txt
check tests regression.sing regression_output.txt
if command -v python3 > /dev/null; then
  cd verification || exit 1
  for s in test_sslib.py verify_examples.py controls.py verify_new_examples.py check_session_outputs.py; do
    last=$(python3 "$s" | tail -1)
    echo "[....] verification/$s: $last"
    case "$last" in *FAIL*|*mismatches\ [1-9]*) status=1 ;; esac
  done
  echo "(randomised check: python3 verification/crosscheck_v11.py 300 11 [1])"
fi
exit $status
