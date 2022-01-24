(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_di:B. forall b_dh:B. C(b_di & b_dh)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_di () (Bag Int))

(assert (bag.subbag b_di UNIVERALSET))
(assert (>= (* 2 (bag.card b_di)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_dh () (Bag Int))

(assert (bag.subbag b_dh UNIVERALSET))
(assert (>= (* 2 (bag.card b_dh)) (+ (+ n (* 3 t)) 1)))


(assert (not (>= (* 2 (bag.card (bag.inter_min b_di b_dh))) (+ (- n t) 1))))

(check-sat)
