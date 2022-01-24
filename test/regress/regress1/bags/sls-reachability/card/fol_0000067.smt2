(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_cc:C. nonempty(c_cc & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cc () (Bag Int))

(assert (bag.subbag c_cc UNIVERALSET))
(assert (>= (* 2 (bag.card c_cc)) (+ (- n t) 1)))


(assert
 (= (bag.card (bag.inter_min c_cc (bag.difference_subtract UNIVERALSET f))) 0))

(check-sat)
