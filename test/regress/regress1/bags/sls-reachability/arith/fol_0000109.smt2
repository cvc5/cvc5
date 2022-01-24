(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_eu:A. 2a_eu + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_eu () Int)

(assert (<= a_eu n))
(assert (>= a_eu 0))
(assert (>= a_eu (- n t)))


(assert
 (and
  (<
   (* 2 (- (+ (* 2 a_eu) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
