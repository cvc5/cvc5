; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 3))
(declare-const y (_ BitVec 3))
(assert (not (= (bvxor x y) (bvxor y x))))
(check-sat)
(exit)
