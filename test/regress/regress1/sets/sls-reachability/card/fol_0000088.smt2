(set-logic ALL)

(set-info :status unsat)

; forall a_ds:A. forall a_dr:A. nonempty(a_ds & a_dr & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_ds () (Set Int))

(assert (set.subset a_ds UNIVERALSET))
(assert (>= (set.card a_ds) (- n t)))

(declare-fun a_dr () (Set Int))

(assert (set.subset a_dr UNIVERALSET))
(assert (>= (set.card a_dr) (- n t)))


(assert
  (= (set.card (set.inter (set.inter a_ds a_dr) (set.minus UNIVERALSET f))) 0))

(check-sat)
