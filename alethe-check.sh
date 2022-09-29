#!/bin/bash

./prod/bin/cvc5 --produce-proofs --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 --dump-proofs $@ > tmp.alethe
tail -n +2 tmp.alethe > pf.alethe
alethe-proof-checker check pf.alethe $1
