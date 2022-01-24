(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_fc:B. 2b_fc + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_fc () Int)

(assert (<= b_fc n))
(assert (>= b_fc 0))
(assert (>= (* 2 b_fc) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (* 2 b_fc) (bag.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
