; COMMAND-LINE: --bool-to-bv
; EXPECT: sat
(set-logic QF_BV)
(declare-fun x2 () (_ BitVec 3))
(declare-fun x1 () (_ BitVec 3))
(declare-fun x0 () (_ BitVec 3))
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (not (bvult (bvudiv (bvudiv (bvudiv x0 x0) x1) x2) x1)))
(assert (= #b000 x2))
(assert (=> b1 b2))
(check-sat)
