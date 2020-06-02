; COMMAND-LINE: --unconstrained-simp
; EXPECT: unsat
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-fun a () Real)
(assert (= (to_int a) 2))
(assert (= (to_int (/ a 2.0)) 2))
(check-sat)
