(set-logic QF_S)
(set-option :strings-exp true)
(set-info :status unsat)

(declare-fun s () String)

(assert (not (str.contains s "x")))
(assert (str.contains s "xy"))

(check-sat)
