; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try
(set-logic ALL)
(declare-fun a () Real)
(assert (distinct a (sin 2.0)))
(check-sat)
