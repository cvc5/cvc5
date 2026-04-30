; REQUIRES: normaliz
(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :quiet true)
(set-info :status sat)
(assert 
 (int.star-contains 
  (lambda ((x Int) (y Int)) 
    (and 
      (>= (+ (* 5 x) (* 2 y)) 17)
      (<= (- (* 3 x) y) 8)
      (<= (+ (* 2 x) (* 3 y)) 20)
    )
  )
  5 5))

(check-sat)
