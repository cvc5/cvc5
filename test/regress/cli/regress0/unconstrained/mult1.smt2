; COMMAND-LINE: --unconstrained-simp
(set-logic QF_LIA)
(set-info :status sat)

(declare-fun x3 () Int)
(assert (<= (* 1 x3) 0))

(check-sat)
(exit)
