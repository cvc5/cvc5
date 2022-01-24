(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_u:A. 2a_u + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_u () Int)

(assert (<= a_u n))
(assert (>= a_u 0))
(assert (>= a_u (- n t)))


(assert
 (and
  (<
   (* 2 (- (+ (* 2 a_u) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
