; COMMAND-LINE: --nl-ext
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(assert (or (> (sin 0.8) 0.9) (< (sin (- 0.7)) (- 0.75)) (= (sin 3.0) 0.8)))
(check-sat)
