; COMMAND-LINE: --enum-inst-interleave
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((a Real)) (or (> 0 a) (> a 0.0))))
(check-sat)
