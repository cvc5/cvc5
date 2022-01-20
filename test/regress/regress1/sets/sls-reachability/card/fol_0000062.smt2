(set-logic ALL)

(set-info :status sat)

; forall c_by:C. C(c_by & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_by () (Set Int))

(assert (set.subset c_by UNIVERALSET))
(assert (>= (* 2 (set.card c_by)) (+ (- n t) 1)))


(assert
  (not
    (>= (* 2 (set.card (set.inter c_by (set.minus UNIVERALSET f)))) (+ (- n t) 1))))

(check-sat)
