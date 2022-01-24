(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_ec:C. nonempty(c_ec & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ec () (Bag Int))

(assert (bag.subbag c_ec UNIVERALSET))
(assert (>= (* 2 (bag.card c_ec)) (+ (- n t) 1)))


(assert
 (= (bag.card (bag.inter_min c_ec (bag.difference_subtract UNIVERALSET f))) 0))

(check-sat)
