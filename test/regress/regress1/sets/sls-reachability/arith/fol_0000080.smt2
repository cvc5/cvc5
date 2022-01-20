(set-logic ALL)
(set-info :status sat)

; forall b_cx:B. 2b_cx + |UNIVERALSET| - 2n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_cx () Int)
(assert (<= b_cx n))
(assert (>= b_cx 0))
(assert (>= (* 2 b_cx) (+ (+ n (* 3 t)) 1)))


(assert (and (< (* 2 (- (+ (* 2 b_cx) (set.card UNIVERALSET)) (* 2 n))) (+ (+ n (* 3 t)) 1)) (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
