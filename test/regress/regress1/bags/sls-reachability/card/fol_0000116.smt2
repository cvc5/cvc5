(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_gx:B. forall b_gw:B. forall a_gv:A. nonempty(b_gx & b_gw & a_gv)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_gx () (Bag Int))

(assert (bag.subbag b_gx UNIVERALSET))
(assert (>= (* 2 (bag.card b_gx)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gw () (Bag Int))

(assert (bag.subbag b_gw UNIVERALSET))
(assert (>= (* 2 (bag.card b_gw)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_gv () (Bag Int))

(assert (bag.subbag a_gv UNIVERALSET))
(assert (>= (bag.card a_gv) (- n t)))


(assert (= (bag.card (bag.inter_min (bag.inter_min b_gx b_gw) a_gv)) 0))

(check-sat)
