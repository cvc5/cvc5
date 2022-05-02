; EXPECT: unsat
; COMMAND-LINE: --sygus-inference -q
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: lfsc
(set-logic ALL)
(declare-fun v () Bool)
(assert false)
(assert v)
(check-sat)
(exit)
