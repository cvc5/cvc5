(set-logic ALL)

(set-info :status unsat)

; forall a_gn:A. forall a_gm:A. nonempty(a_gn & a_gm & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_gn () (Set Int))

(assert (set.subset a_gn UNIVERALSET))
(assert (>= (set.card a_gn) (- n t)))

(declare-fun a_gm () (Set Int))

(assert (set.subset a_gm UNIVERALSET))
(assert (>= (set.card a_gm) (- n t)))


(assert
  (= (set.card (set.inter (set.inter a_gn a_gm) (set.minus UNIVERALSET f))) 0))

(check-sat)
