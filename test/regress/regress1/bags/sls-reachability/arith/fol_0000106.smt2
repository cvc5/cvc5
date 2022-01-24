(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_ep:B. forall a_eo:A. 2b_ep + 2a_eo + |~f| - 4n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_ep () Int)

(assert (<= b_ep n))
(assert (>= b_ep 0))
(assert (>= (* 2 b_ep) (+ (+ n (* 3 t)) 1)))

(declare-fun a_eo () Int)

(assert (<= a_eo n))
(assert (>= a_eo 0))
(assert (>= a_eo (- n t)))


(assert
 (and
  (<
   (* 2
      (-
       (+ (+ (* 2 b_ep) (* 2 a_eo)) (bag.card (bag.difference_subtract UNIVERALSET f)))
       (* 4 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
