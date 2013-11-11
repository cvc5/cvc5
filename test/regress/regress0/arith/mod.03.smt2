; EXPECT: unknown
(set-logic QF_NIA)
(set-info :smt-lib-version 2.0)
(set-info :status unknown)
(declare-fun n () Int)
(declare-fun x () Int)

(assert (< (mod x n) 0))
(assert (< (div x n) 0))

(check-sat)
