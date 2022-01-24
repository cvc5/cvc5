(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_ch:C. forall b_cg:B. 2c_ch + b_cg + |~f| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ch () Int)

(assert (<= c_ch n))
(assert (>= c_ch 0))
(assert (>= (* 2 c_ch) (+ (- n t) 1)))

(declare-fun b_cg () Int)

(assert (<= b_cg n))
(assert (>= b_cg 0))
(assert (>= (* 2 b_cg) (+ (+ n (* 3 t)) 1)))


(assert
 (and
  (<
   (- (+ (+ (* 2 c_ch) b_cg) (bag.card (bag.difference_subtract UNIVERALSET f)))
      (* 3 n))
   1)
  (> 1 0)))

(check-sat)
