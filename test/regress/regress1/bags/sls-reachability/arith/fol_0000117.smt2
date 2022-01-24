(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_ff:B. 3b_ff + |UNIVERALSET| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_ff () Int)

(assert (<= b_ff n))
(assert (>= b_ff 0))
(assert (>= (* 2 b_ff) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (* 3 b_ff) (bag.card UNIVERALSET)) (* 3 n)) 1) (> 1 0)))

(check-sat)
