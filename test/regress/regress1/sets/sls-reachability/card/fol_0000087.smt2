(set-logic ALL)

(set-info :status unsat)

; forall c_dq:C. forall a_dp:A. nonempty(c_dq & a_dp)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dq () (Set Int))

(assert (set.subset c_dq UNIVERALSET))
(assert (>= (* 2 (set.card c_dq)) (+ (- n t) 1)))

(declare-fun a_dp () (Set Int))

(assert (set.subset a_dp UNIVERALSET))
(assert (>= (set.card a_dp) (- n t)))


(assert (= (set.card (set.inter c_dq a_dp)) 0))

(check-sat)
