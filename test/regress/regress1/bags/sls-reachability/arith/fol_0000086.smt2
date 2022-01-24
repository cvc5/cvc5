(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_de:A. a_de + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_de () Int)

(assert (<= a_de n))
(assert (>= a_de 0))
(assert (>= a_de (- n t)))


(assert
 (and (< (- (+ a_de (bag.card (bag.difference_subtract UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
