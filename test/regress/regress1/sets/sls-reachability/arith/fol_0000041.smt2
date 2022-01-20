(set-logic ALL)
(set-info :status sat)

; forall c_r:C. c_r + |UNIVERALSET| - n >= n or n <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_r () Int)
(assert (<= c_r n))
(assert (>= c_r 0))
(assert (>= (* 2 c_r) (+ (- n t) 1)))


(assert (and (< (- (+ c_r (set.card UNIVERALSET)) n) n) (> n 0)))

(check-sat)
