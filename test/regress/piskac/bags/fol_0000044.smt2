(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall nonempty_s:nonempty. nonempty_s + |UNIVERALSET| - n >= n or n <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun nonempty_s () Int)

(assert (<= nonempty_s n))
(assert (>= nonempty_s 0))
(assert (>= nonempty_s 1))


(assert (and (< (- (+ nonempty_s (bag.card UNIVERALSET)) n) n) (> n 0)))

(check-sat)
