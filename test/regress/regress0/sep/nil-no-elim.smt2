(set-logic ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-heap (U Int))

(assert (= (as sep.nil U) (f a)))

(assert (pto (f a) 0))

(check-sat)
