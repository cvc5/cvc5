(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_c:B. b_c + |UNIVERALSET| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_c () Int)

(assert (<= b_c n))
(assert (>= b_c 0))
(assert (>= (* 2 b_c) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ b_c (bag.card UNIVERALSET)) n) (- n t)) (> (- n t) 0)))

(check-sat)
