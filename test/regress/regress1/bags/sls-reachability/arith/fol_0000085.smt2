(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall c_dd:C. c_dd + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dd () Int)

(assert (<= c_dd n))
(assert (>= c_dd 0))
(assert (>= (* 2 c_dd) (+ (- n t) 1)))


(assert
 (and (< (- (+ c_dd (bag.card (bag.difference_subtract UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
