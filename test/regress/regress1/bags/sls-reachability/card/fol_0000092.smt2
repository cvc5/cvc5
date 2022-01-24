(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_dz:C. forall a_dy:A. nonempty(c_dz & a_dy)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dz () (Bag Int))

(assert (bag.subbag c_dz UNIVERALSET))
(assert (>= (* 2 (bag.card c_dz)) (+ (- n t) 1)))

(declare-fun a_dy () (Bag Int))

(assert (bag.subbag a_dy UNIVERALSET))
(assert (>= (bag.card a_dy) (- n t)))


(assert (= (bag.card (bag.inter_min c_dz a_dy)) 0))

(check-sat)
