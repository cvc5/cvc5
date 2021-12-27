(set-logic ALL)
(set-info :status unsat)

; forall a_bq:A. a_bq + |~f| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_bq () Int)
(assert (<= a_bq n))
(assert (>= a_bq 0))
(assert (>= a_bq (- n t)))


(assert (and (< (- (+ a_bq (set.card (set.minus UNIVERALSET f))) n) (- n t)) (> (- n t) 0)))

(check-sat)
