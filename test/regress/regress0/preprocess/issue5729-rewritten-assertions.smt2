; EXPECT: sat
(set-logic QF_ALL)
(declare-fun x () (_ BitVec 1))
(assert (= (_ bv0 1) ((_ int2bv 1) (bv2nat x))))
(check-sat)
