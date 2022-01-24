(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_ek:B. forall a_ej:A. forall a_ei:A. nonempty(b_ek & a_ej & a_ei & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_ek () (Bag Int))

(assert (bag.subbag b_ek UNIVERALSET))
(assert (>= (* 2 (bag.card b_ek)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ej () (Bag Int))

(assert (bag.subbag a_ej UNIVERALSET))
(assert (>= (bag.card a_ej) (- n t)))

(declare-fun a_ei () (Bag Int))

(assert (bag.subbag a_ei UNIVERALSET))
(assert (>= (bag.card a_ei) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min (bag.inter_min b_ek a_ej) a_ei)
                  (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
