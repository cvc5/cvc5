(set-logic ALL)

(set-info :status unsat)

; forall c_bz:C. C(c_bz)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bz () (Set Int))

(assert (set.subset c_bz UNIVERALSET))
(assert (>= (* 2 (set.card c_bz)) (+ (- n t) 1)))


(assert (not (>= (* 2 (set.card c_bz)) (+ (- n t) 1))))

(check-sat)
