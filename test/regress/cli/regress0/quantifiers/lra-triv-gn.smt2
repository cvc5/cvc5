; REQUIRES: unrestricted-mode
; COMMAND-LINE: --global-negate
; EXPECT: unsat
; Proofs and unsat cores are not supported with --global-negate: its unsat
; answer does not establish that the original assertions are inconsistent.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic LRA)
(set-info :status unsat)
(assert (not (exists ((?X Real)) (>= (/ (- 13) 4) ?X))))
(check-sat)
(exit)
