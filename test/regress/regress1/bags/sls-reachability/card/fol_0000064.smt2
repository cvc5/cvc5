(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_bz:C. C(c_bz)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bz () (Bag Int))

(assert (bag.subbag c_bz UNIVERALSET))
(assert (>= (* 2 (bag.card c_bz)) (+ (- n t) 1)))


(assert (not (>= (* 2 (bag.card c_bz)) (+ (- n t) 1))))

(check-sat)
