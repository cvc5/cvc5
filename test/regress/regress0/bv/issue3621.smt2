(set-logic QF_BVLIA)
(declare-fun a () (_ BitVec 1))
(assert (< (bv2nat a) 1))
(check-sat)
