; COMMAND-LINE: --arith-rewrite-equalities -i
; EXPECT: sat
(set-logic QF_NIA)
(set-info :status sat)
(declare-const i4 Int)
(declare-const v9 Bool)
(assert (= v9 (< (- i4) 1)))
(push)
(check-sat)
