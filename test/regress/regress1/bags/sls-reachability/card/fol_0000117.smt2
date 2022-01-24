(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_ha:B. forall b_gz:B. forall b_gy:B. nonempty(b_ha & b_gz & b_gy)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_ha () (Bag Int))

(assert (bag.subbag b_ha UNIVERALSET))
(assert (>= (* 2 (bag.card b_ha)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gz () (Bag Int))

(assert (bag.subbag b_gz UNIVERALSET))
(assert (>= (* 2 (bag.card b_gz)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gy () (Bag Int))

(assert (bag.subbag b_gy UNIVERALSET))
(assert (>= (* 2 (bag.card b_gy)) (+ (+ n (* 3 t)) 1)))


(assert (= (bag.card (bag.inter_min (bag.inter_min b_ha b_gz) b_gy)) 0))

(check-sat)
