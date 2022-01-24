(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_bq:A. a_bq + |~f| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_bq () Int)

(assert (<= a_bq n))
(assert (>= a_bq 0))
(assert (>= a_bq (- n t)))


(assert
 (and
  (< (- (+ a_bq (bag.card (bag.difference_subtract UNIVERALSET f))) n) (- n t))
  (> (- n t) 0)))

(check-sat)
