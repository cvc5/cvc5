(set-logic ALL)
(set-info :status unsat)

; forall a_dh:A. 2a_dh + |~f| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_dh () Int)
(assert (<= a_dh n))
(assert (>= a_dh 0))
(assert (>= a_dh (- n t)))


(assert (and (< (- (+ (* 2 a_dh) (set.card (set.minus UNIVERALSET f))) (* 2 n)) 1) (> 1 0)))

(check-sat)
