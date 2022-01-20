(set-logic ALL)
(set-info :status sat)

; forall nonempty_i:nonempty. nonempty_i + |UNIVERALSET| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun nonempty_i () Int)
(assert (<= nonempty_i n))
(assert (>= nonempty_i 0))
(assert (>= nonempty_i 1))


(assert (and (< (- (+ nonempty_i (set.card UNIVERALSET)) n) (- n t)) (> (- n t) 0)))

(check-sat)
