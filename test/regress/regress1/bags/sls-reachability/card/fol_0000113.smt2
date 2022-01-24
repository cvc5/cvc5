(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_gq:C. forall b_gp:B. forall b_go:B. nonempty(c_gq & b_gp & b_go)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_gq () (Bag Int))

(assert (bag.subbag c_gq UNIVERALSET))
(assert (>= (* 2 (bag.card c_gq)) (+ (- n t) 1)))

(declare-fun b_gp () (Bag Int))

(assert (bag.subbag b_gp UNIVERALSET))
(assert (>= (* 2 (bag.card b_gp)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_go () (Bag Int))

(assert (bag.subbag b_go UNIVERALSET))
(assert (>= (* 2 (bag.card b_go)) (+ (+ n (* 3 t)) 1)))


(assert (= (bag.card (bag.inter_min (bag.inter_min c_gq b_gp) b_go)) 0))

(check-sat)
