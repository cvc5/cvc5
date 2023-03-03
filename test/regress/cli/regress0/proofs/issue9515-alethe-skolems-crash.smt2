; COMMAND-LINE: --dump-proofs --proof-format-mode=alethe --dag-thresh=0 --simplification=none --proof-granularity=theory-rewrite
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic QF_UF)
(declare-sort u 0)
(declare-fun $2 () Bool)
(declare-fun y () u)
(declare-fun $ () u)
(assert (= y (ite $2 y $)))
(assert (not $2))
(assert (not (= $ y)))
(check-sat)
