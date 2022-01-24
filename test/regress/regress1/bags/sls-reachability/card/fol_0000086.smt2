(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_do:A. nonempty(a_do & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_do () (Bag Int))

(assert (bag.subbag a_do UNIVERALSET))
(assert (>= (bag.card a_do) (- n t)))


(assert
 (= (bag.card (bag.inter_min a_do (bag.difference_subtract UNIVERALSET f))) 0))

(check-sat)
