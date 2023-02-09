; COMMAND-LINE: --dump-proofs --proof-format-mode=alethe --dag-thresh=0 --simplification=none --proof-granularity=theory-rewrite --no-proof-alethe-res-pivots
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic QF_UF)
(declare-sort I 0)
(declare-fun o (I I) I)
(declare-fun e () I)
(declare-fun e0 () I)
(assert (or (= e0 (o e0 e0)) (= e (o e0 e))))
(assert (and (not (= e0 (o e0 e0))) (not (= e (o e0 e)))))
(check-sat)