(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_gb:B. forall b_ga:B. forall a_fz:A. forall a_fy:A. forall a_fx:A. nonempty(b_gb & b_ga & a_fz & a_fy & a_fx)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_gb () (Bag Int))

(assert (bag.subbag b_gb UNIVERALSET))
(assert (>= (* 2 (bag.card b_gb)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_ga () (Bag Int))

(assert (bag.subbag b_ga UNIVERALSET))
(assert (>= (* 2 (bag.card b_ga)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fz () (Bag Int))

(assert (bag.subbag a_fz UNIVERALSET))
(assert (>= (bag.card a_fz) (- n t)))

(declare-fun a_fy () (Bag Int))

(assert (bag.subbag a_fy UNIVERALSET))
(assert (>= (bag.card a_fy) (- n t)))

(declare-fun a_fx () (Bag Int))

(assert (bag.subbag a_fx UNIVERALSET))
(assert (>= (bag.card a_fx) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min
    (bag.inter_min (bag.inter_min (bag.inter_min b_gb b_ga) a_fz) a_fy) a_fx))
  0))

(check-sat)
