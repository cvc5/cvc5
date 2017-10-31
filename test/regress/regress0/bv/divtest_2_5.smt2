; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-logic QF_BV)
(set-info :status sat)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(assert (not (= (bvudiv x (_ bv0 8)) (_ bv255 8))))
(check-sat)
