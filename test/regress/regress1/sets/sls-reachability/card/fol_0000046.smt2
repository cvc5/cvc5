(set-logic ALL)

(set-info :status sat)

; forall a_v:A. forall a_u:A. C(a_v & a_u & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_v () (Set Int))

(assert (set.subset a_v UNIVERALSET))
(assert (>= (set.card a_v) (- n t)))

(declare-fun a_u () (Set Int))

(assert (set.subset a_u UNIVERALSET))
(assert (>= (set.card a_u) (- n t)))


(assert
  (not
    (>= (* 2 (set.card (set.inter (set.inter a_v a_u) (set.minus UNIVERALSET f))))
        (+ (- n t) 1))))

(check-sat)
