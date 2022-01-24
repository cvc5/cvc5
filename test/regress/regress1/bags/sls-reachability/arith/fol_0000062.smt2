(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_bu:C. c_bu + |~f| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bu () Int)

(assert (<= c_bu n))
(assert (>= c_bu 0))
(assert (>= (* 2 c_bu) (+ (- n t) 1)))


(assert
 (and
  (< (* 2 (- (+ c_bu (bag.card (bag.difference_subtract UNIVERALSET f))) n))
     (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
