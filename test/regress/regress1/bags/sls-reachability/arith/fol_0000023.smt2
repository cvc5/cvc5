(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_f:B. b_f + |UNIVERALSET| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_f () Int)

(assert (<= b_f n))
(assert (>= b_f 0))
(assert (>= (* 2 b_f) (+ (+ n (* 3 t)) 1)))


(assert
 (and (< (* 2 (- (+ b_f (bag.card UNIVERALSET)) n)) (+ (- n t) 1))
      (> (+ (- n t) 1) (* 2 0))))

(check-sat)
