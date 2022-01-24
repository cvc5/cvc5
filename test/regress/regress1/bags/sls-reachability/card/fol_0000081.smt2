(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_dg:B. B(b_dg)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_dg () (Bag Int))

(assert (bag.subbag b_dg UNIVERALSET))
(assert (>= (* 2 (bag.card b_dg)) (+ (+ n (* 3 t)) 1)))


(assert (not (>= (* 2 (bag.card b_dg)) (+ (+ n (* 3 t)) 1))))

(check-sat)
