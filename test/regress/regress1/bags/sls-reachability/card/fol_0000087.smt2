(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_dq:C. forall a_dp:A. nonempty(c_dq & a_dp)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dq () (Bag Int))

(assert (bag.subbag c_dq UNIVERALSET))
(assert (>= (* 2 (bag.card c_dq)) (+ (- n t) 1)))

(declare-fun a_dp () (Bag Int))

(assert (bag.subbag a_dp UNIVERALSET))
(assert (>= (bag.card a_dp) (- n t)))


(assert (= (bag.card (bag.inter_min c_dq a_dp)) 0))

(check-sat)
