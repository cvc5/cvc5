; COMMAND-LINE: --cbqi-recurse
; EXPECT: unsat
(set-logic LIA)
(assert (forall ((U Int) (V Int)) (not (= (* 3 U) (+ 22 (* (- 5) V)))) ) )
(check-sat)
