; COMMAND-LINE: --check-proofs --tlimit-per=1000
; EXPECT: unknown
(set-logic ALL)
(assert
 (forall ((x Int) (y Int) (a Real) (z Int))
  (or (> 0.0 (* (/ x y) (/ (* y 2) 0.0)))
      (< 0.0 (/ a 2 y (/ (* z z) (to_real x)))))))
(check-sat)
