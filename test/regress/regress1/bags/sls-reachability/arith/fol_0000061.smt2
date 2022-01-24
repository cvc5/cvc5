(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_bt:A. a_bt + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_bt () Int)

(assert (<= a_bt n))
(assert (>= a_bt 0))
(assert (>= a_bt (- n t)))


(assert
 (and (< (- (+ a_bt (bag.card (bag.difference_subtract UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
