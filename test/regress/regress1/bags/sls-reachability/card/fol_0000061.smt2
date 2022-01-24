(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_bx:A. nonempty(a_bx & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_bx () (Bag Int))

(assert (bag.subbag a_bx UNIVERALSET))
(assert (>= (bag.card a_bx) (- n t)))


(assert
 (= (bag.card (bag.inter_min a_bx (bag.difference_subtract UNIVERALSET f))) 0))

(check-sat)
