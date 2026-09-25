; REQUIRES: unrestricted-mode
; EXPECT: unsat
; COMMAND-LINE: --sygus-inference=try -q
; --sygus-inference is not supported with full proofs.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-fun v () Bool)
(assert false)
(assert v)
(check-sat)
(exit)
