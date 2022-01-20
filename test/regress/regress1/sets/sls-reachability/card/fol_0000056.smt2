(set-logic ALL)

(set-info :status sat)

; forall b_bt:B. forall a_bs:A. forall a_br:A. top(b_bt & a_bs & a_br)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_bt () (Set Int))

(assert (set.subset b_bt UNIVERALSET))
(assert (>= (* 2 (set.card b_bt)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bs () (Set Int))

(assert (set.subset a_bs UNIVERALSET))
(assert (>= (set.card a_bs) (- n t)))

(declare-fun a_br () (Set Int))

(assert (set.subset a_br UNIVERALSET))
(assert (>= (set.card a_br) (- n t)))


(assert
  (>= (set.card (set.minus UNIVERALSET (set.inter (set.inter b_bt a_bs) a_br))) 1))

(check-sat)
