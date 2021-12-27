(set-logic ALL)
(set-info :status unsat)

; forall c_dk:C. 2c_dk + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dk () Int)
(assert (<= c_dk n))
(assert (>= c_dk 0))
(assert (>= (* 2 c_dk) (+ (- n t) 1)))


(assert (and (< (- (+ (* 2 c_dk) (set.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
