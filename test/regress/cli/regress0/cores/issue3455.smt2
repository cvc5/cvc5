; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-fun x0 () Real)
(check-sat)
(assert (<= (* x0 (- 1.0)) 0.0))
(assert (or (>= 0.0 x0) (> (+ 1.0 x0) (- 12.0))))
(check-sat)
(push)
(assert (<= x0 (- 13.0)))
(check-sat)
(check-sat)
(check-sat)
