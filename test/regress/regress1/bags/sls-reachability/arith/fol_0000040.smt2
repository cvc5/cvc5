(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall top_q:top. top_q + |UNIVERALSET| - n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun top_q () Int)

(assert (<= top_q n))
(assert (>= top_q 0))
(assert (>= top_q n))


(assert
 (and (< (* 2 (- (+ top_q (bag.card UNIVERALSET)) n)) (+ (+ n (* 3 t)) 1))
      (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
