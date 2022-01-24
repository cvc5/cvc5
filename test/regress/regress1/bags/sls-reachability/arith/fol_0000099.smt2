(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_dy:B. forall a_dx:A. 3b_dy + 2a_dx + |~f| - 5n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_dy () Int)

(assert (<= b_dy n))
(assert (>= b_dy 0))
(assert (>= (* 2 b_dy) (+ (+ n (* 3 t)) 1)))

(declare-fun a_dx () Int)

(assert (<= a_dx n))
(assert (>= a_dx 0))
(assert (>= a_dx (- n t)))


(assert
 (and
  (<
   (-
    (+ (+ (* 3 b_dy) (* 2 a_dx)) (bag.card (bag.difference_subtract UNIVERALSET f)))
    (* 5 n))
   1)
  (> 1 0)))

(check-sat)
