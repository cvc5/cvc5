(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_ez:C. forall b_ey:B. c_ez + 2b_ey + |UNIVERALSET| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ez () Int)

(assert (<= c_ez n))
(assert (>= c_ez 0))
(assert (>= (* 2 c_ez) (+ (- n t) 1)))

(declare-fun b_ey () Int)

(assert (<= b_ey n))
(assert (>= b_ey 0))
(assert (>= (* 2 b_ey) (+ (+ n (* 3 t)) 1)))


(assert
 (and (< (- (+ (+ c_ez (* 2 b_ey)) (bag.card UNIVERALSET)) (* 3 n)) 1) (> 1 0)))

(check-sat)
