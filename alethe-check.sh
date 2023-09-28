#!/bin/bash

# tfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1
tfile="/home/hbarbosa/cvc/wt-proofnew/pf.alethe"

./prod/bin/cvc5 --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 --dump-proofs --proof-alethe-res-pivots --dag-thresh=0  $@ | tail -n +2 > $tfile
carcara check --allow-int-real-subtyping --expand-let-bindings --skip-unknown-rules $tfile $1
