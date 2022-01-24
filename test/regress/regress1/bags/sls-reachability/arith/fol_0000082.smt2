(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_cz:B. 2b_cz + |UNIVERALSET| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_cz () Int)

(assert (<= b_cz n))
(assert (>= b_cz 0))
(assert (>= (* 2 b_cz) (+ (+ n (* 3 t)) 1)))


(assert
 (and (< (* 2 (- (+ (* 2 b_cz) (bag.card UNIVERALSET)) (* 2 n))) (+ (- n t) 1))
      (> (+ (- n t) 1) (* 2 0))))

(check-sat)
