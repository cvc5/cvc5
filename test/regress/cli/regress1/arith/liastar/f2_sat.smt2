(set-logic ALL)
(set-option :produce-models true)
;; (set-info :status sat)
(assert 
 (int.star-contains 
  ((x Int) (y Int)) 
  (and 
    (>= (+ (* 5 x) (* 2 y)) 17)
    (<= (- (* 3 x) y) 8)
    (<= (+ (* 2 x) (* 3 y)) 20)
  )
  (tuple 5 5)))

(check-sat)
