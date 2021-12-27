(set-logic ALL)
(set-info :status unsat)

; forall a_br:A. a_br + |UNIVERALSET| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_br () Int)
(assert (<= a_br n))
(assert (>= a_br 0))
(assert (>= a_br (- n t)))


(assert (and (< (- (+ a_br (set.card UNIVERALSET)) n) (- n t)) (> (- n t) 0)))

(check-sat)
