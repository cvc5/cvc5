(set-logic LIA)
(set-info :status sat)

(define-fun findIdx ((y1 Int)(y2 Int)(k1 Int)) Int (div (* (- 7) (mod y1 (- 5))) 2))
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun k () Int)

(assert (not (and (=> (< x1 x2) (=> (< k x1) (= (findIdx x1 x2 k) 0)))
  (=> (< x1 x2) (=> (> k x2) (= (findIdx x1 x2 k) 2)))
  (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 k) 1))))))
(check-sat)
