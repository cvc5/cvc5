; EXPECT: unsat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun v () Bool)
(assert false)
(assert v)
(check-sat)
(exit)
