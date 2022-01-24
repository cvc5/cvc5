(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_dp:C. forall b_do:B. c_dp + b_do + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dp () Int)

(assert (<= c_dp n))
(assert (>= c_dp 0))
(assert (>= (* 2 c_dp) (+ (- n t) 1)))

(declare-fun b_do () Int)

(assert (<= b_do n))
(assert (>= b_do 0))
(assert (>= (* 2 b_do) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (+ c_dp b_do) (bag.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
