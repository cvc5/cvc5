(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cq:C. forall b_cp:B. c_cq + b_cp + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cq () Int)

(assert (<= c_cq n))
(assert (>= c_cq 0))
(assert (>= (* 2 c_cq) (+ (- n t) 1)))

(declare-fun b_cp () Int)

(assert (<= b_cp n))
(assert (>= b_cp 0))
(assert (>= (* 2 b_cp) (+ (+ n (* 3 t)) 1)))


(assert
 (and
  (<
   (* 2
      (- (+ (+ c_cq b_cp) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
