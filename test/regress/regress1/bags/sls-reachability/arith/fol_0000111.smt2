(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_ew:A. 2a_ew + |UNIVERALSET| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_ew () Int)

(assert (<= a_ew n))
(assert (>= a_ew 0))
(assert (>= a_ew (- n t)))


(assert
 (and (< (* 2 (- (+ (* 2 a_ew) (bag.card UNIVERALSET)) (* 2 n))) (+ (- n t) 1))
      (> (+ (- n t) 1) (* 2 0))))

(check-sat)
