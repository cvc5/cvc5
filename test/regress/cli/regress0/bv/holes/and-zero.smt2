; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x1 (_ BitVec 3))
(assert (not (= (bvand x1 #b000) #b000)))
(check-sat)
(exit)
