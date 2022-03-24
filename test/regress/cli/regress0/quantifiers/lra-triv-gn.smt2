; COMMAND-LINE: --global-negate
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic LRA)
(set-info :status unsat)
(assert (not (exists ((?X Real)) (>= (/ (- 13) 4) ?X))))
(check-sat)
(exit)
