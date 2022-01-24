(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall nonempty_m:nonempty. nonempty_m + |UNIVERALSET| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun nonempty_m () Int)

(assert (<= nonempty_m n))
(assert (>= nonempty_m 0))
(assert (>= nonempty_m 1))


(assert
 (and (< (* 2 (- (+ nonempty_m (bag.card UNIVERALSET)) n)) (+ (- n t) 1))
      (> (+ (- n t) 1) (* 2 0))))

(check-sat)
