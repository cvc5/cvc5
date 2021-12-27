(set-logic ALL)
(set-info :status unsat)

; forall c_bv:C. c_bv + |UNIVERALSET| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bv () Int)
(assert (<= c_bv n))
(assert (>= c_bv 0))
(assert (>= (* 2 c_bv) (+ (- n t) 1)))


(assert (and (< (* 2 (- (+ c_bv (set.card UNIVERALSET)) n)) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
