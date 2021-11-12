#!/bin/bash

./prod/bin/cvc5 --proof-format-mode=alethe --dag-thresh=0 $@ > tmp.alethe
tail -n +2 tmp.alethe > pf.alethe
alethe-proof-checker check pf.alethe $1
