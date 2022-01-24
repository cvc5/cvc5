(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_da:B. 2b_da + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_da () Int)

(assert (<= b_da n))
(assert (>= b_da 0))
(assert (>= (* 2 b_da) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (* 2 b_da) (bag.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
