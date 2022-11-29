(set-logic LIRA)
(set-info :status unsat)
(assert (forall ((x Int) (y Int) (a Real) (z Int)) (or (> (to_real x) (+ a (* (/ 2 3) (to_real y)) (* (/ 4 5) (to_real z)))) (< (to_real x) (+ 10.0 (* 3.0 a) (* (/ 2 5) (to_real y)) (* (/ 4 7) (to_real z)))))))
(check-sat)
