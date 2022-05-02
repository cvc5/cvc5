; EXPECT: unsat
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-fun n () Real)
(declare-fun x () Real)

; This example is to exercise the model builder with unknown results

(assert (>= n 1))
(assert (<= n 1))
(assert (<= x 1))
(assert (>= x 1))
(assert (not (= (* x n) 1)))

(check-sat)
