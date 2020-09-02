; COMMAND-LINE: --quiet
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (and (= (bvudiv (_ bv2 4) x) (_ bv2 4)) (= (_ bv0 4) x) (= (_ bv1 4) x)))
(check-sat)
(exit)
