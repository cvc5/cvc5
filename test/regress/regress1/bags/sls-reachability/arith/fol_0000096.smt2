(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_ds:A. 3a_ds + |~f| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_ds () Int)

(assert (<= a_ds n))
(assert (>= a_ds 0))
(assert (>= a_ds (- n t)))


(assert
 (and
  (< (- (+ (* 3 a_ds) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 3 n)) 1)
  (> 1 0)))

(check-sat)
