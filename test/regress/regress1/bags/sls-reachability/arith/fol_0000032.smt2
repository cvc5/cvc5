(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_j:B. b_j + |UNIVERALSET| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_j () Int)

(assert (<= b_j n))
(assert (>= b_j 0))
(assert (>= (* 2 b_j) (+ (+ n (* 3 t)) 1)))


(assert (and (< (- (+ b_j (bag.card UNIVERALSET)) n) 1) (> 1 0)))

(check-sat)
