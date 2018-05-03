(set-logic AUFBVDTNIRA)
(set-info :status unsat)
(declare-fun abs1 (Int) Int)
(assert
  (forall ((x Int) (y Int))
  (! (= (<= (abs1 x) y) (and (<= (- y) x) (<= x y))) :pattern ((abs1 x) y) )))
(assert (< (abs1 (- 3)) 3))
(check-sat)
