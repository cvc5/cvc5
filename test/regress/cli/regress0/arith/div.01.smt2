(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-fun n () Int)

(assert (= n 0))
(assert (= (div (div n n) n)
           (div (div (div n n) n) n)))
(assert (distinct (div (div n n) n)
                  (div (div (div (div (div n n) n) n) n) n)))

(check-sat)
