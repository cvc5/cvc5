(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_dx:C. nonempty(c_dx)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dx () (Bag Int))

(assert (bag.subbag c_dx UNIVERALSET))
(assert (>= (* 2 (bag.card c_dx)) (+ (- n t) 1)))


(assert (= (bag.card c_dx) 0))

(check-sat)
