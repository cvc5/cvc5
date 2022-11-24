#!/bin/bash

# tfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1
tfile="/home/hbarbosa/cvc/wt-diff/pf.alethe"

./prod/bin/cvc5 --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 --dump-proofs  --proof-alethe-res-pivots $@ | tail -n +2 > $tfile
carcara check --allow-int-real-subtyping --expand-let-bindings $tfile $1
