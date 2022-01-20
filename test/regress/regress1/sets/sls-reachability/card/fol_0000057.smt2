(set-logic ALL)

(set-info :status sat)

; forall a_bu:A. A(a_bu & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_bu () (Set Int))

(assert (set.subset a_bu UNIVERALSET))
(assert (>= (set.card a_bu) (- n t)))


(assert (not (>= (set.card (set.inter a_bu (set.minus UNIVERALSET f))) (- n t))))

(check-sat)
