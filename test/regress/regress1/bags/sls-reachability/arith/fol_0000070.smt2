(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_cd:C. forall b_cc:B. c_cd + b_cc + |~f| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cd () Int)

(assert (<= c_cd n))
(assert (>= c_cd 0))
(assert (>= (* 2 c_cd) (+ (- n t) 1)))

(declare-fun b_cc () Int)

(assert (<= b_cc n))
(assert (>= b_cc 0))
(assert (>= (* 2 b_cc) (+ (+ n (* 3 t)) 1)))


(assert
 (and
  (<
   (- (+ (+ c_cd b_cc) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n))
   1)
  (> 1 0)))

(check-sat)
