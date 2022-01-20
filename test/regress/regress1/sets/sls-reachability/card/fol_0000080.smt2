(set-logic ALL)

(set-info :status sat)

; forall b_df:B. forall b_de:B. B(b_df & b_de)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_df () (Set Int))

(assert (set.subset b_df UNIVERALSET))
(assert (>= (* 2 (set.card b_df)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_de () (Set Int))

(assert (set.subset b_de UNIVERALSET))
(assert (>= (* 2 (set.card b_de)) (+ (+ n (* 3 t)) 1)))


(assert (not (>= (* 2 (set.card (set.inter b_df b_de))) (+ (+ n (* 3 t)) 1))))

(check-sat)
