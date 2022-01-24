(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_eh:A. forall a_eg:A. forall a_ef:A. nonempty(a_eh & a_eg & a_ef & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_eh () (Bag Int))

(assert (bag.subbag a_eh UNIVERALSET))
(assert (>= (bag.card a_eh) (- n t)))

(declare-fun a_eg () (Bag Int))

(assert (bag.subbag a_eg UNIVERALSET))
(assert (>= (bag.card a_eg) (- n t)))

(declare-fun a_ef () (Bag Int))

(assert (bag.subbag a_ef UNIVERALSET))
(assert (>= (bag.card a_ef) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min (bag.inter_min a_eh a_eg) a_ef)
                  (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
