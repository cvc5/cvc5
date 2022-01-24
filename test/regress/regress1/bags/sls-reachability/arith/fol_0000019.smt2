(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_b:A. a_b + |UNIVERALSET| - n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_b () Int)

(assert (<= a_b n))
(assert (>= a_b 0))
(assert (>= a_b (- n t)))


(assert
 (and (< (* 2 (- (+ a_b (bag.card UNIVERALSET)) n)) (+ (+ n (* 3 t)) 1))
      (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
