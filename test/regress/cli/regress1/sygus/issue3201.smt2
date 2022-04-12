; EXPECT: unsat
; COMMAND-LINE: --sygus-inference -q
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-fun v () Bool)
(assert false)
(assert v)
(check-sat)
(exit)
