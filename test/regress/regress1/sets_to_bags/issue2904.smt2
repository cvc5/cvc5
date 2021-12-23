(set-logic ALL)
(set-option :fmf-bound true)
(set-info :status unsat)
; conjecture set nonempty(~b & ~c)

(declare-fun n () Int)
(declare-fun f () Int)
(declare-fun m () Int)

(declare-fun b () (Bag Int))
(declare-fun c () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))
(assert (bag.subbag b UNIVERALSET))
(assert (bag.subbag c UNIVERALSET))

(assert (> n 0))
(assert (= (bag.card UNIVERALSET) n))
(assert (= (bag.card b) m))
(assert (= (bag.card c) (- f m)))
(assert (>= m 0))
(assert (>= f m))
(assert (> n (+ (* 2 f) m)))


(assert (>= (bag.card (bag.difference_remove UNIVERALSET (bag.inter_min (bag.difference_remove UNIVERALSET b) (bag.difference_remove UNIVERALSET c)))) n))

(check-sat)
