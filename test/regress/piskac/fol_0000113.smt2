(set-logic ALL)
(set-info :status unsat)

; forall c_ez:C. forall b_ey:B. c_ez + 2b_ey + |UNIVERALSET| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_ez () Int)
(assert (<= c_ez n))
(assert (>= c_ez 0))
(assert (>= (* 2 c_ez) (+ (- n t) 1)))

(declare-fun b_ey () Int)
(assert (<= b_ey n))
(assert (>= b_ey 0))
(assert (>= (* 2 b_ey) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (+ c_ez (* 2 b_ey)) (set.card UNIVERALSET)) (* 3 n)) 1) (> 1 0)))

(check-sat)
