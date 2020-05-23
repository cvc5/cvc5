; COMMAND-LINE: --unconstrained-simp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () Real)
(assert (is_int x))
(assert (is_int (+ x 1)))
(check-sat)
