(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cm:C. 2c_cm + |~f| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cm () Int)

(assert (<= c_cm n))
(assert (>= c_cm 0))
(assert (>= (* 2 c_cm) (+ (- n t) 1)))


(assert
 (and
  (< (- (+ (* 2 c_cm) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)) 1)
  (> 1 0)))

(check-sat)
