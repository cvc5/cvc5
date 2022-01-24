(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_bn:B. forall a_bm:A. b_bn + 2a_bm + |UNIVERALSET| - 3n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bn () Int)

(assert (<= b_bn n))
(assert (>= b_bn 0))
(assert (>= (* 2 b_bn) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bm () Int)

(assert (<= a_bm n))
(assert (>= a_bm 0))
(assert (>= a_bm (- n t)))


(assert
 (and
  (< (* 2 (- (+ (+ b_bn (* 2 a_bm)) (bag.card UNIVERALSET)) (* 3 n))) (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
