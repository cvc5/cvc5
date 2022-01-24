(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_l:C. c_l + |UNIVERALSET| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_l () Int)

(assert (<= c_l n))
(assert (>= c_l 0))
(assert (>= (* 2 c_l) (+ (- n t) 1)))


(assert (and (< (- (+ c_l (bag.card UNIVERALSET)) n) 1) (> 1 0)))

(check-sat)
