(set-logic LIRA)
(set-info :status unsat)
(assert (forall ((X Real) (Y Real)) (or (not (is_int X)) (not (>= (+ X (* (- (/ 2 3)) Y)) (- (/ 1 6)))) (not (>= (+ (* (- 1.0) X) (* (- (/ 1 4)) Y)) (- (/ 61 8)))) (not (>= (+ (* (- 1.0) X) (* (/ 5 2) Y)) 13.0))) ))
(check-sat)
