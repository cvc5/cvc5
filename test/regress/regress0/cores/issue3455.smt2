; COMMAND-LINE: -q --incremental --no-check-proofs
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(declare-fun x0 () Real)
(check-sat)
(assert (<= (* x0 (- 1)) 0))
(assert (or (>= 0 x0) (> (+ 1.0 x0) (- 12))))
(check-sat)
(push)
(assert (<= x0 (- 13)))
(check-sat)
(check-sat)
(check-sat)