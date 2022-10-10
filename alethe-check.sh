#!/bin/bash

./prod/bin/cvc5 --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 --dump-proofs $@ > tmp.alethe
tail -n +2 tmp.alethe > pf.alethe
alethe-proof-checker check --allow-int-real-subtyping pf.alethe $1
