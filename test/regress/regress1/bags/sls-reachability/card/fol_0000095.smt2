(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_ee:A. forall a_ed:A. nonempty(a_ee & a_ed & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_ee () (Bag Int))

(assert (bag.subbag a_ee UNIVERALSET))
(assert (>= (bag.card a_ee) (- n t)))

(declare-fun a_ed () (Bag Int))

(assert (bag.subbag a_ed UNIVERALSET))
(assert (>= (bag.card a_ed) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min a_ee a_ed) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
