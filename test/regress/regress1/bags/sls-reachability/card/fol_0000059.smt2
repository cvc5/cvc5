(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_bv:A. A(a_bv)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_bv () (Bag Int))

(assert (bag.subbag a_bv UNIVERALSET))
(assert (>= (bag.card a_bv) (- n t)))


(assert (not (>= (bag.card a_bv) (- n t))))

(check-sat)
