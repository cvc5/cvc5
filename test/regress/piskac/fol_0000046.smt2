(set-logic ALL)
(set-info :status unsat)

; forall a_u:A. 2a_u + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_u () Int)
(assert (<= a_u n))
(assert (>= a_u 0))
(assert (>= a_u (- n t)))


(assert (and (< (* 2 (- (+ (* 2 a_u) (set.card (set.minus UNIVERALSET f))) (* 2 n))) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
