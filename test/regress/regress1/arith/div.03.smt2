; EXPECT: unsat
(set-logic QF_NIA)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun n () Int)

(assert (> n 0))
(assert (>= x n))
(assert (< (div x n) 1))

(check-sat)
