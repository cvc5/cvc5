(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_bv:C. c_bv + |UNIVERALSET| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bv () Int)

(assert (<= c_bv n))
(assert (>= c_bv 0))
(assert (>= (* 2 c_bv) (+ (- n t) 1)))


(assert
 (and (< (* 2 (- (+ c_bv (bag.card UNIVERALSET)) n)) (+ (- n t) 1))
      (> (+ (- n t) 1) (* 2 0))))

(check-sat)
