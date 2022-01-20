(set-logic ALL)

(set-info :status sat)

; forall b_di:B. forall b_dh:B. C(b_di & b_dh)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_di () (Set Int))

(assert (set.subset b_di UNIVERALSET))
(assert (>= (* 2 (set.card b_di)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_dh () (Set Int))

(assert (set.subset b_dh UNIVERALSET))
(assert (>= (* 2 (set.card b_dh)) (+ (+ n (* 3 t)) 1)))


(assert (not (>= (* 2 (set.card (set.inter b_di b_dh))) (+ (- n t) 1))))

(check-sat)
