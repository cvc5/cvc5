(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-fun n () Int)


(assert (= (div n n) (div (div n n) n)))
(assert (distinct (div (div n n) n) (div (div (div n n) n) n)))
(assert (<= n 0))
(assert (>= n 0))
(check-sat)
