(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_dw:C. forall c_dv:C. nonempty(c_dw & c_dv)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dw () (Bag Int))

(assert (bag.subbag c_dw UNIVERALSET))
(assert (>= (* 2 (bag.card c_dw)) (+ (- n t) 1)))

(declare-fun c_dv () (Bag Int))

(assert (bag.subbag c_dv UNIVERALSET))
(assert (>= (* 2 (bag.card c_dv)) (+ (- n t) 1)))


(assert (= (bag.card (bag.inter_min c_dw c_dv)) 0))

(check-sat)
