(set-logic ALL)
(set-info :status unsat)

; forall c_dp:C. forall b_do:B. c_dp + b_do + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dp () Int)
(assert (<= c_dp n))
(assert (>= c_dp 0))
(assert (>= (* 2 c_dp) (+ (- n t) 1)))

(declare-fun b_do () Int)
(assert (<= b_do n))
(assert (>= b_do 0))
(assert (>= (* 2 b_do) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (+ c_dp b_do) (set.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
