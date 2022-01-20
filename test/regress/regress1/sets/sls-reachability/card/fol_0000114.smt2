(set-logic ALL)

(set-info :status unsat)

; forall c_gs:C. forall b_gr:B. nonempty(c_gs & b_gr)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_gs () (Set Int))

(assert (set.subset c_gs UNIVERALSET))
(assert (>= (* 2 (set.card c_gs)) (+ (- n t) 1)))

(declare-fun b_gr () (Set Int))

(assert (set.subset b_gr UNIVERALSET))
(assert (>= (* 2 (set.card b_gr)) (+ (+ n (* 3 t)) 1)))


(assert (= (set.card (set.inter c_gs b_gr)) 0))

(check-sat)
