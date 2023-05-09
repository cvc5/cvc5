; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 16))
(assert (not (= (concat ((_ extract 5 3) x) ((_ extract 2 1) x)) ((_ extract 5 1) x))))
(check-sat)
(exit)
