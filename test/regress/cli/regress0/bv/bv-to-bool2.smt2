; COMMAND-LINE: --bv-to-bool
; EXPECT: sat
(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 1))
(declare-fun v2 () (_ BitVec 1))

(assert (= (bvxor v2 v1) v1))


(check-sat)
(exit)
