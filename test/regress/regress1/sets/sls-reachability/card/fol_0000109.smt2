(set-logic ALL)

(set-info :status sat)

; forall a_gi:A. forall a_gh:A. C(a_gi & a_gh & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_gi () (Set Int))

(assert (set.subset a_gi UNIVERALSET))
(assert (>= (set.card a_gi) (- n t)))

(declare-fun a_gh () (Set Int))

(assert (set.subset a_gh UNIVERALSET))
(assert (>= (set.card a_gh) (- n t)))


(assert
  (not
    (>=
      (* 2 (set.card (set.inter (set.inter a_gi a_gh) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
