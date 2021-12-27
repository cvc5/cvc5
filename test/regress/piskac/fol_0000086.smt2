(set-logic ALL)
(set-info :status unsat)

; forall a_de:A. a_de + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_de () Int)
(assert (<= a_de n))
(assert (>= a_de 0))
(assert (>= a_de (- n t)))


(assert (and (< (- (+ a_de (set.card (set.minus UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
