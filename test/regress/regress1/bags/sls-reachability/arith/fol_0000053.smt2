(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_bj:B. forall a_bi:A. b_bj + a_bi + |~f| - 2n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bj () Int)

(assert (<= b_bj n))
(assert (>= b_bj 0))
(assert (>= (* 2 b_bj) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bi () Int)

(assert (<= a_bi n))
(assert (>= a_bi 0))
(assert (>= a_bi (- n t)))


(assert
 (and
  (<
   (* 2
      (- (+ (+ b_bj a_bi) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (+ n (* 3 t)) 1))
  (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
