(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_bh:C. forall b_bg:B. c_bh + b_bg + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bh () Int)

(assert (<= c_bh n))
(assert (>= c_bh 0))
(assert (>= (* 2 c_bh) (+ (- n t) 1)))

(declare-fun b_bg () Int)

(assert (<= b_bg n))
(assert (>= b_bg 0))
(assert (>= (* 2 b_bg) (+ (+ n (* 3 t)) 1)))


(assert
 (and
  (<
   (* 2
      (- (+ (+ c_bh b_bg) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
