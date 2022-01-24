(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall nonempty_k:nonempty. nonempty_k + |UNIVERALSET| - n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun nonempty_k () Int)

(assert (<= nonempty_k n))
(assert (>= nonempty_k 0))
(assert (>= nonempty_k 1))


(assert
 (and (< (* 2 (- (+ nonempty_k (bag.card UNIVERALSET)) n)) (+ (+ n (* 3 t)) 1))
      (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
