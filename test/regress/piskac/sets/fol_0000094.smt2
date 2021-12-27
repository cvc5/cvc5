(set-logic ALL)
(set-info :status unsat)

; forall c_dq:C. c_dq + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dq () Int)
(assert (<= c_dq n))
(assert (>= c_dq 0))
(assert (>= (* 2 c_dq) (+ (- n t) 1)))


(assert (and (< (- (+ c_dq (set.card (set.minus UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
