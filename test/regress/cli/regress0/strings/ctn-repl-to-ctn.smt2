(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (=
(str.contains (str.replace x y x) y) (str.contains x y)
)))
(check-sat)
