(set-logic ALL)

(set-info :status unsat)

; forall a_ee:A. forall a_ed:A. nonempty(a_ee & a_ed & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_ee () (Set Int))

(assert (set.subset a_ee UNIVERALSET))
(assert (>= (set.card a_ee) (- n t)))

(declare-fun a_ed () (Set Int))

(assert (set.subset a_ed UNIVERALSET))
(assert (>= (set.card a_ed) (- n t)))


(assert
  (= (set.card (set.inter (set.inter a_ee a_ed) (set.minus UNIVERALSET f))) 0))

(check-sat)
