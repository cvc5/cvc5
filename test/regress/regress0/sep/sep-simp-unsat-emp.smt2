(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun a () U)
(declare-fun b () U)

(assert (emp x x))
(assert (sep (pto x a) (pto y b)))
(check-sat)
