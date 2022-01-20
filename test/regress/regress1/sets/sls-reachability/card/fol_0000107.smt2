(set-logic ALL)

(set-info :status unsat)

; forall b_gb:B. forall b_ga:B. forall a_fz:A. forall a_fy:A. forall a_fx:A. nonempty(b_gb & b_ga & a_fz & a_fy & a_fx)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_gb () (Set Int))

(assert (set.subset b_gb UNIVERALSET))
(assert (>= (* 2 (set.card b_gb)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_ga () (Set Int))

(assert (set.subset b_ga UNIVERALSET))
(assert (>= (* 2 (set.card b_ga)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fz () (Set Int))

(assert (set.subset a_fz UNIVERALSET))
(assert (>= (set.card a_fz) (- n t)))

(declare-fun a_fy () (Set Int))

(assert (set.subset a_fy UNIVERALSET))
(assert (>= (set.card a_fy) (- n t)))

(declare-fun a_fx () (Set Int))

(assert (set.subset a_fx UNIVERALSET))
(assert (>= (set.card a_fx) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter (set.inter b_gb b_ga) a_fz) a_fy) a_fx))
    0))

(check-sat)
