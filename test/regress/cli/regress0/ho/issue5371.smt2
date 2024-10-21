; COMMAND-LINE:
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun a (Bool) Bool)
(assert (a false))
(assert (a true))
(check-sat)
