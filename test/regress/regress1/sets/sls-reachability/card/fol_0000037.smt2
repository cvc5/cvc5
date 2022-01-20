(set-logic ALL)

(set-info :status sat)

; forall a_n:A. a_n + |UNIVERALSET| - n >= n or n <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_n () Int)

(assert (<= a_n n))
(assert (>= a_n 0))
(assert (>= a_n (- n t)))


(assert (and (< (- (+ a_n (set.card UNIVERALSET)) n) n) (> n 0)))

(check-sat)
