(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_bf:B. forall a_be:A. b_bf + a_be + |~f| - 2n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bf () Int)

(assert (<= b_bf n))
(assert (>= b_bf 0))
(assert (>= (* 2 b_bf) (+ (+ n (* 3 t)) 1)))

(declare-fun a_be () Int)

(assert (<= a_be n))
(assert (>= a_be 0))
(assert (>= a_be (- n t)))


(assert
 (and
  (<
   (- (+ (+ b_bf a_be) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n))
   (- n t))
  (> (- n t) 0)))

(check-sat)
