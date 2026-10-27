; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (= (bvadd x x) (bvmul x #b00010))))
(check-sat)
(exit)
