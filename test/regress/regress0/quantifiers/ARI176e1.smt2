; COMMAND-LINE: --cbqi-recurse
; EXPECT: unsat
(set-logic UFLIA)
(assert (forall ((U Int) (V Int)) (not (= (* 3 U) (+ 22 (* (- 5) V)))) ) )
(check-sat)
