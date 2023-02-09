; COMMAND-LINE: --dump-proofs --proof-format-mode=alethe --dag-thresh=0 --simplification=none --proof-granularity=theory-rewrite --proof-alethe-res-pivots
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic QF_UF)
(declare-sort I 0)
(declare-fun o (I I) I)
(declare-fun e4 () I)
(declare-fun e2 () I)
(declare-fun e () I)
(assert (and (or (= e4 (o e4 e)) (= e4 (o e4 e4)) (= e4 (o e4 e2))) (or (= (o e4 e4) (o (o e4 e2) e2)) (= (o e4 e) (o (o e4 e2) e2))) (or (= e2 (o e4 e)) (= e2 (o e4 e4)) (= e2 (o e4 (o (o e4 e2) e2)))) (= (o e4 e2) (o e (o (o e4 e2) e2))) (or (= e4 (o (o (o e4 e2) e2) (o e4 e2))) (= e4 (o e (o (o e4 e2) e2))) (= e4 (o (o e4 e2) e))) (or (= e (o e4 e4)) (= e2 (o e4 e2)))))
(assert (and (not (= (o e4 e4) (o (o e4 e2) e4))) (not (= (o e2 e4) (o (o e4 e2) e4)))))
(assert (and (= (o e4 e2) (o e4 (o e4 e2))) (= (o e4 e2) (o (o (o e4 e2) e2) (o e4 e2)))))
(check-sat)