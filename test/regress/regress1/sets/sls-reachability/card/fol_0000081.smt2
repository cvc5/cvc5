(set-logic ALL)

(set-info :status unsat)

; forall b_dg:B. B(b_dg)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_dg () (Set Int))

(assert (set.subset b_dg UNIVERALSET))
(assert (>= (* 2 (set.card b_dg)) (+ (+ n (* 3 t)) 1)))


(assert (not (>= (* 2 (set.card b_dg)) (+ (+ n (* 3 t)) 1))))

(check-sat)
