(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_bx:B. b_bx + |~f| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bx () Int)

(assert (<= b_bx n))
(assert (>= b_bx 0))
(assert (>= (* 2 b_bx) (+ (+ n (* 3 t)) 1)))


(assert
 (and
  (< (* 2 (- (+ b_bx (bag.card (bag.difference_subtract UNIVERALSET f))) n))
     (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
