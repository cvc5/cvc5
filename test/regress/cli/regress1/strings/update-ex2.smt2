(set-logic QF_SLIA)

(set-info :status unsat)
(declare-fun s () String)

(assert (not (= (str.substr (str.update "AAAAAA" 1 s) 5 1) "A")))
(assert (< (str.len s) 3))

(check-sat)
