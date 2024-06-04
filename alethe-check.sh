#!/bin/bash

tfile="$(mktemp /tmp/fooXXXXXXXXX.alethe)" || exit 1
fileName="$(echo $tfile | rev | cut -d'/' -f1 | rev | cut -d'.' -f1)"


ulimit -S -t 30 -s 8589934592; ~/cvc5/wt-proofnew/prod/bin/cvc5 --proof-format-mode=alethe --lang=smt2 --dump-proofs --proof-alethe-res-pivots --enum-inst $@ | tail -n +2 > $tfile
# 8gb stack size
~/carcara/wt-bv/target/release/carcara check --allow-int-real-subtyping --expand-let-bindings -i $tfile $1 > /tmp/$fileName.output
if ! grep -q "invalid" /tmp/$fileName.output; then
  echo "success --- ./alethe-check-cvc.sh $1"
else
  echo "invalid --- ./alethe-check-cvc.sh $1"
fi
echo "/tmp/$fileName.alethe"
echo "==================="
