; COMMAND-LINE: --fmf-bound
; EXPECT: sat
(set-logic ALL)
(declare-sort S 0)
(declare-fun c () S)
(declare-fun b () S)
(declare-fun d (S Int) Bool)
(assert (distinct b c))
(assert (forall ((e S) (f Int)) (=> (and (> f 1) (< f 0)) (d e f))))
(check-sat)
