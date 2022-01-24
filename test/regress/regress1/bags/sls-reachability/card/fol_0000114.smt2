(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_gs:C. forall b_gr:B. nonempty(c_gs & b_gr)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_gs () (Bag Int))

(assert (bag.subbag c_gs UNIVERALSET))
(assert (>= (* 2 (bag.card c_gs)) (+ (- n t) 1)))

(declare-fun b_gr () (Bag Int))

(assert (bag.subbag b_gr UNIVERALSET))
(assert (>= (* 2 (bag.card b_gr)) (+ (+ n (* 3 t)) 1)))


(assert (= (bag.card (bag.inter_min c_gs b_gr)) 0))

(check-sat)
