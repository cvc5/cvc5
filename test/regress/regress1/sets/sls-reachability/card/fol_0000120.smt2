(set-logic ALL)

(set-info :status unsat)

; forall a_hi:A. forall a_hh:A. forall a_hg:A. nonempty(a_hi & a_hh & a_hg)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_hi () (Set Int))

(assert (set.subset a_hi UNIVERALSET))
(assert (>= (set.card a_hi) (- n t)))

(declare-fun a_hh () (Set Int))

(assert (set.subset a_hh UNIVERALSET))
(assert (>= (set.card a_hh) (- n t)))

(declare-fun a_hg () (Set Int))

(assert (set.subset a_hg UNIVERALSET))
(assert (>= (set.card a_hg) (- n t)))


(assert (= (set.card (set.inter (set.inter a_hi a_hh) a_hg)) 0))

(check-sat)
