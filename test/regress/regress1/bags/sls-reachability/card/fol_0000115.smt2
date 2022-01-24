(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_gu:B. forall b_gt:B. nonempty(b_gu & b_gt)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_gu () (Bag Int))

(assert (bag.subbag b_gu UNIVERALSET))
(assert (>= (* 2 (bag.card b_gu)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gt () (Bag Int))

(assert (bag.subbag b_gt UNIVERALSET))
(assert (>= (* 2 (bag.card b_gt)) (+ (+ n (* 3 t)) 1)))


(assert (= (bag.card (bag.inter_min b_gu b_gt)) 0))

(check-sat)
