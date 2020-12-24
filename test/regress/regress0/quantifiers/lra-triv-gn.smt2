; COMMAND-LINE: --global-negate --no-check-unsat-cores --no-check-unsat-cores-new
; EXPECT: unsat
(set-logic LRA)
(set-info :status unsat)
(assert (not (exists ((?X Real)) (>= (/ (- 13) 4) ?X))))
(check-sat)
(exit)
