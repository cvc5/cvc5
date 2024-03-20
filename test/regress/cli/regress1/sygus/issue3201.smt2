; EXPECT: unsat
; COMMAND-LINE: --sygus-inference=try -q
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-fun v () Bool)
(assert false)
(assert v)
(check-sat)
(exit)
