; COMMAND-LINE: --dump-proofs --proof-format-mode=alethe --dag-thresh=0 --simplification=none --proof-granularity=theory-rewrite
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic QF_UF)
(declare-sort u 0)
(declare-fun $2 () Bool)
(declare-fun $ () u)
(declare-fun s () u)
(assert (not (= s (ite $2 s $))))
(assert (not (= $ (ite $2 s $))))
(check-sat)
