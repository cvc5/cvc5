(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_eb:C. forall b_ea:B. nonempty(c_eb & b_ea)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_eb () (Bag Int))

(assert (bag.subbag c_eb UNIVERALSET))
(assert (>= (* 2 (bag.card c_eb)) (+ (- n t) 1)))

(declare-fun b_ea () (Bag Int))

(assert (bag.subbag b_ea UNIVERALSET))
(assert (>= (* 2 (bag.card b_ea)) (+ (+ n (* 3 t)) 1)))


(assert (= (bag.card (bag.inter_min c_eb b_ea)) 0))

(check-sat)
