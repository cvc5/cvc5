(set-logic ALL)
(set-info :status unsat)

; forall a_bt:A. a_bt + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_bt () Int)
(assert (<= a_bt n))
(assert (>= a_bt 0))
(assert (>= a_bt (- n t)))


(assert (and (< (- (+ a_bt (set.card (set.minus UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
