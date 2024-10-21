(set-logic QF_SLIA)

(set-info :status sat)
(declare-fun s () String)

(assert (not (= (str.substr (str.update "AAAAAA" 1 s) 5 1) "A")))

(check-sat)
