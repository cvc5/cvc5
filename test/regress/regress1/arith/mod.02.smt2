; EXPECT: unsat
(set-logic QF_NIA)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun n () Int)

(assert (distinct n 0))
(assert (> (mod n n) 0))

(check-sat)
