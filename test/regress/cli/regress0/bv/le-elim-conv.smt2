(declare-fun a () (_ BitVec 32))

(assert (>= (bv2nat a) 50000))
(assert (<= (bv2nat a) 60000))

(check-sat)
