(set-logic ALL)

(set-info :status sat)

; forall c_dm:C. forall a_dl:A. nonempty(c_dm & a_dl & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dm () (Set Int))

(assert (set.subset c_dm UNIVERALSET))
(assert (>= (* 2 (set.card c_dm)) (+ (- n t) 1)))

(declare-fun a_dl () (Set Int))

(assert (set.subset a_dl UNIVERALSET))
(assert (>= (set.card a_dl) (- n t)))


(assert
  (= (set.card (set.inter (set.inter c_dm a_dl) (set.minus UNIVERALSET f))) 0))

(check-sat)
