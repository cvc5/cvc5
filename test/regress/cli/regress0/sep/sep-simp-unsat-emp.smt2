(set-logic QF_ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-heap (U U))

(declare-fun x () U)
(declare-fun y () U)
(declare-fun a () U)
(declare-fun b () U)

(assert sep.emp)
(assert (sep (pto x a) (pto y b)))
(check-sat)
