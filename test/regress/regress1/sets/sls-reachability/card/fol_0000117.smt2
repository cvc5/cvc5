(set-logic ALL)

(set-info :status sat)

; forall b_ha:B. forall b_gz:B. forall b_gy:B. nonempty(b_ha & b_gz & b_gy)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_ha () (Set Int))

(assert (set.subset b_ha UNIVERALSET))
(assert (>= (* 2 (set.card b_ha)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gz () (Set Int))

(assert (set.subset b_gz UNIVERALSET))
(assert (>= (* 2 (set.card b_gz)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gy () (Set Int))

(assert (set.subset b_gy UNIVERALSET))
(assert (>= (* 2 (set.card b_gy)) (+ (+ n (* 3 t)) 1)))


(assert (= (set.card (set.inter (set.inter b_ha b_gz) b_gy)) 0))

(check-sat)
