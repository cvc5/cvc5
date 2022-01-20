(set-logic ALL)

(set-info :status sat)

; forall a_eh:A. forall a_eg:A. forall a_ef:A. nonempty(a_eh & a_eg & a_ef & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_eh () (Set Int))

(assert (set.subset a_eh UNIVERALSET))
(assert (>= (set.card a_eh) (- n t)))

(declare-fun a_eg () (Set Int))

(assert (set.subset a_eg UNIVERALSET))
(assert (>= (set.card a_eg) (- n t)))

(declare-fun a_ef () (Set Int))

(assert (set.subset a_ef UNIVERALSET))
(assert (>= (set.card a_ef) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter a_eh a_eg) a_ef) (set.minus UNIVERALSET f)))
    0))

(check-sat)
