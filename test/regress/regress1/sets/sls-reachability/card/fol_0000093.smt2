(set-logic ALL)

(set-info :status unsat)

; forall c_eb:C. forall b_ea:B. nonempty(c_eb & b_ea)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_eb () (Set Int))

(assert (set.subset c_eb UNIVERALSET))
(assert (>= (* 2 (set.card c_eb)) (+ (- n t) 1)))

(declare-fun b_ea () (Set Int))

(assert (set.subset b_ea UNIVERALSET))
(assert (>= (* 2 (set.card b_ea)) (+ (+ n (* 3 t)) 1)))


(assert (= (set.card (set.inter c_eb b_ea)) 0))

(check-sat)
