(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_da:C. forall b_cz:B. forall a_cy:A. nonempty(c_da & b_cz & a_cy)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_da () (Bag Int))

(assert (bag.subbag c_da UNIVERALSET))
(assert (>= (* 2 (bag.card c_da)) (+ (- n t) 1)))

(declare-fun b_cz () (Bag Int))

(assert (bag.subbag b_cz UNIVERALSET))
(assert (>= (* 2 (bag.card b_cz)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_cy () (Bag Int))

(assert (bag.subbag a_cy UNIVERALSET))
(assert (>= (bag.card a_cy) (- n t)))


(assert (= (bag.card (bag.inter_min (bag.inter_min c_da b_cz) a_cy)) 0))

(check-sat)
