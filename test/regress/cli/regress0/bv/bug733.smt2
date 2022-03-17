; EXPECT: sat
(set-logic QF_BV)
(declare-fun x2 () (_ BitVec 3))
(declare-fun x1 () (_ BitVec 3))
(declare-fun x0 () (_ BitVec 3))
(assert (not (bvult (bvudiv (bvudiv (bvudiv x0 x0) x1) x2) x1)))
(assert (= #b000 x2))
(check-sat)
