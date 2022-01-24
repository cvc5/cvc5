(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall nonempty_i:nonempty. nonempty_i + |UNIVERALSET| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun nonempty_i () Int)

(assert (<= nonempty_i n))
(assert (>= nonempty_i 0))
(assert (>= nonempty_i 1))


(assert
 (and (< (- (+ nonempty_i (bag.card UNIVERALSET)) n) (- n t)) (> (- n t) 0)))

(check-sat)
