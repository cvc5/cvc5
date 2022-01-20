(set-logic ALL)

(set-info :status sat)

; forall c_cf:C. forall a_ce:A. nonempty(c_cf & a_ce & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cf () (Set Int))

(assert (set.subset c_cf UNIVERALSET))
(assert (>= (* 2 (set.card c_cf)) (+ (- n t) 1)))

(declare-fun a_ce () (Set Int))

(assert (set.subset a_ce UNIVERALSET))
(assert (>= (set.card a_ce) (- n t)))


(assert
  (= (set.card (set.inter (set.inter c_cf a_ce) (set.minus UNIVERALSET f))) 0))

(check-sat)
