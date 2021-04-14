; EXPECT: unsat
; COMMAND-LINE: --sygus-inference -q
(set-logic ALL)
(declare-fun v () Bool)
(assert false)
(assert v)
(check-sat)
(exit)
