(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_w:B. forall a_v:A. b_w + a_v + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_w () Int)

(assert (<= b_w n))
(assert (>= b_w 0))
(assert (>= (* 2 b_w) (+ (+ n (* 3 t)) 1)))

(declare-fun a_v () Int)

(assert (<= a_v n))
(assert (>= a_v 0))
(assert (>= a_v (- n t)))


(assert
 (and
  (<
   (* 2
      (- (+ (+ b_w a_v) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
