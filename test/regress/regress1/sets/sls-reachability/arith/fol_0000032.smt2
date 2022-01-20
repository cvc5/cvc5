(set-logic ALL)
(set-info :status unsat)

; forall b_j:B. b_j + |UNIVERALSET| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_j () Int)
(assert (<= b_j n))
(assert (>= b_j 0))
(assert (>= (* 2 b_j) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ b_j (set.card UNIVERALSET)) n) 1) (> 1 0)))

(check-sat)
