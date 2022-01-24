(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_hi:A. forall a_hh:A. forall a_hg:A. nonempty(a_hi & a_hh & a_hg)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_hi () (Bag Int))

(assert (bag.subbag a_hi UNIVERALSET))
(assert (>= (bag.card a_hi) (- n t)))

(declare-fun a_hh () (Bag Int))

(assert (bag.subbag a_hh UNIVERALSET))
(assert (>= (bag.card a_hh) (- n t)))

(declare-fun a_hg () (Bag Int))

(assert (bag.subbag a_hg UNIVERALSET))
(assert (>= (bag.card a_hg) (- n t)))


(assert (= (bag.card (bag.inter_min (bag.inter_min a_hi a_hh) a_hg)) 0))

(check-sat)
