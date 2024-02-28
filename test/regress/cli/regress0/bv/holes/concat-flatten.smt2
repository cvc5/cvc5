; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x1 (_ BitVec 3))
(declare-const x2 (_ BitVec 4))
(declare-const x3 (_ BitVec 5))
(declare-const x4 (_ BitVec 6))
(assert (not (= (concat (concat x1 x2) (concat x3 x4)) (concat x1 x2 x3 x4))))
(check-sat)
(exit)
