(set-logic LIRA)
(set-info :status unsat)
(assert (forall ((x Int) (y Int) (a Real) (z Int)) (or (> x (+ a (* (/ 2 3) y) (* (/ 4 5) z))) (< x (+ 10 (* 3 a) (* (/ 2 5) y) (* (/ 4 7) z))))))
(check-sat)
