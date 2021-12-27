(set-logic ALL)
(set-info :status unsat)

; forall a_h:A. a_h + |UNIVERALSET| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_h () Int)
(assert (<= a_h n))
(assert (>= a_h 0))
(assert (>= a_h (- n t)))


(assert (and (< (- (+ a_h (set.card UNIVERALSET)) n) 1) (> 1 0)))

(check-sat)
