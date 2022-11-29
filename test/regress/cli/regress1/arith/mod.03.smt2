; EXPECT: sat
(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-fun n () Int)
(declare-fun x () Int)

(assert (< (mod x n) 0))
(assert (< (div x n) 0))

(check-sat)
