; REQUIRES: normaliz
; DISABLE-TESTER: proof
(set-logic HO_ALL)
(set-info :status unsat)
(assert 
 (int.star-contains 
  (lambda ((x Int) (y Int)) 
    (and 
      (>= (+ (* 5 x) (* 2 y)) 17)
      (<= (- (* 3 x) y) 8)
      (<= (+ (* 2 x) (* 3 y)) 20)
    )
  )
  5 4))

(check-sat)
