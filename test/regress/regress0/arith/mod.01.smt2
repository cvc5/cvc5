; EXPECT: unknown
(set-logic QF_NIA)
(set-info :smt-lib-version 2.0)
(set-info :status unknown)
(declare-fun n () Int)
(declare-fun x () Int)

(assert (>= n 1))
(assert (< (mod x n) n))

(check-sat)
