(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_bz:C. c_bz + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bz () Int)

(assert (<= c_bz n))
(assert (>= c_bz 0))
(assert (>= (* 2 c_bz) (+ (- n t) 1)))


(assert
 (and (< (- (+ c_bz (bag.card (bag.difference_subtract UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
