(set-logic ALL)
(set-info :status unsat)

; forall b_ep:B. forall a_eo:A. 2b_ep + 2a_eo + |~f| - 4n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_ep () Int)
(assert (<= b_ep n))
(assert (>= b_ep 0))
(assert (>= (* 2 b_ep) (+ (+ n (* 3 t)) 1)))

(declare-fun a_eo () Int)
(assert (<= a_eo n))
(assert (>= a_eo 0))
(assert (>= a_eo (- n t)))


(assert (and (< (* 2 (- (+ (+ (* 2 b_ep) (* 2 a_eo)) (set.card (set.minus UNIVERALSET f))) (* 4 n))) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
