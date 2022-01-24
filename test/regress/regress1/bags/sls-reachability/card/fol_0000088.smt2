(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_ds:A. forall a_dr:A. nonempty(a_ds & a_dr & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_ds () (Bag Int))

(assert (bag.subbag a_ds UNIVERALSET))
(assert (>= (bag.card a_ds) (- n t)))

(declare-fun a_dr () (Bag Int))

(assert (bag.subbag a_dr UNIVERALSET))
(assert (>= (bag.card a_dr) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min a_ds a_dr) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
