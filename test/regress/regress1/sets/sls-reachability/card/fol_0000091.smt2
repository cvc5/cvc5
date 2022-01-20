(set-logic ALL)

(set-info :status unsat)

; forall c_dx:C. nonempty(c_dx)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dx () (Set Int))

(assert (set.subset c_dx UNIVERALSET))
(assert (>= (* 2 (set.card c_dx)) (+ (- n t) 1)))


(assert (= (set.card c_dx) 0))

(check-sat)
