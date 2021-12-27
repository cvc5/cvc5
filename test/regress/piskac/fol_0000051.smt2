(set-logic ALL)
(set-info :status unsat)

; forall b_bf:B. forall a_be:A. b_bf + a_be + |~f| - 2n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_bf () Int)
(assert (<= b_bf n))
(assert (>= b_bf 0))
(assert (>= (* 2 b_bf) (+ (+ n (* 3 t)) 1)))

(declare-fun a_be () Int)
(assert (<= a_be n))
(assert (>= a_be 0))
(assert (>= a_be (- n t)))


(assert (and (< (- (+ (+ b_bf a_be) (set.card (set.minus UNIVERALSET f))) (* 2 n)) (- n t)) (> (- n t) 0)))

(check-sat)
