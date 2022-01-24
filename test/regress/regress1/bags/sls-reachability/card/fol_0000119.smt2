(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_hf:A. forall a_he:A. nonempty(a_hf & a_he & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_hf () (Bag Int))

(assert (bag.subbag a_hf UNIVERALSET))
(assert (>= (bag.card a_hf) (- n t)))

(declare-fun a_he () (Bag Int))

(assert (bag.subbag a_he UNIVERALSET))
(assert (>= (bag.card a_he) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min a_hf a_he) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
