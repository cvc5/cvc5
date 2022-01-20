(set-logic ALL)
(set-info :status unsat)

; forall c_by:C. c_by + |~f| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_by () Int)
(assert (<= c_by n))
(assert (>= c_by 0))
(assert (>= (* 2 c_by) (+ (- n t) 1)))


(assert (and (< (- (+ c_by (set.card (set.minus UNIVERALSET f))) n) 1) (> 1 0)))

(check-sat)
