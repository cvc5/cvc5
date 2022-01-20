(set-logic ALL)

(set-info :status unsat)

; forall b_ek:B. forall a_ej:A. forall a_ei:A. nonempty(b_ek & a_ej & a_ei & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_ek () (Set Int))

(assert (set.subset b_ek UNIVERALSET))
(assert (>= (* 2 (set.card b_ek)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ej () (Set Int))

(assert (set.subset a_ej UNIVERALSET))
(assert (>= (set.card a_ej) (- n t)))

(declare-fun a_ei () (Set Int))

(assert (set.subset a_ei UNIVERALSET))
(assert (>= (set.card a_ei) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter b_ek a_ej) a_ei) (set.minus UNIVERALSET f)))
    0))

(check-sat)
