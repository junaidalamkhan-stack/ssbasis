#!/bin/sh
# Compile SSOrder.lean and list the axioms each theorem depends on.
# Usage: ./check_axioms.sh [path-to-lean]   (default: lean on PATH)
LEAN=${1:-lean}
cd "$(dirname "$0")" || exit 1
tmp=$(mktemp -d) || exit 1
cp SSOrder.lean "$tmp/SSAxioms.lean"
for t in SS.add_right_cancel SS.lsum_lt_or_eq SS.lsum_le_of_forall2 SS.not_lt_zero \
         SS.zero_le SS.fdeg_lt SS.no_infinite_descent SS.exists_minimal SS.descent_reaches \
         Examples.lex_wf Examples.ex24_degree_drop Examples.ex24_degrees \
         Examples.ex46_formal_vs_actual; do
  echo "#print axioms $t" >> "$tmp/SSAxioms.lean"
done
"$LEAN" "$tmp/SSAxioms.lean" > "$tmp/out.txt" 2>&1; st=$?
if [ $st -eq 0 ] && diff -q "$tmp/out.txt" out_axioms.txt > /dev/null; then
  echo "[ OK ] SSOrder.lean compiles; axioms as in out_axioms.txt"
else
  echo "[DIFF] see $tmp/out.txt"; st=1
fi
exit $st
