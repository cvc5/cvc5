(set-logic ALL)
(set-info :status unsat)

; forall c_cf:C. forall b_ce:B. c_cf + 2b_ce + |~f| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cf () Int)
(assert (<= c_cf n))
(assert (>= c_cf 0))
(assert (>= (* 2 c_cf) (+ (- n t) 1)))

(declare-fun b_ce () Int)
(assert (<= b_ce n))
(assert (>= b_ce 0))
(assert (>= (* 2 b_ce) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ (+ c_cf (* 2 b_ce)) (set.card (set.minus UNIVERALSET f))) (* 3 n)) 1) (> 1 0)))

(check-sat)
