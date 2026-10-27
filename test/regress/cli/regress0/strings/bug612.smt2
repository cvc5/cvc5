(set-logic QF_S)

(set-info :status unsat)

(declare-fun s () String)

(assert (not (str.contains s "x")))
(assert (str.contains s "xy"))

(check-sat)
