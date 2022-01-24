(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_gn:A. forall a_gm:A. nonempty(a_gn & a_gm & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_gn () (Bag Int))

(assert (bag.subbag a_gn UNIVERALSET))
(assert (>= (bag.card a_gn) (- n t)))

(declare-fun a_gm () (Bag Int))

(assert (bag.subbag a_gm UNIVERALSET))
(assert (>= (bag.card a_gm) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min a_gn a_gm) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
