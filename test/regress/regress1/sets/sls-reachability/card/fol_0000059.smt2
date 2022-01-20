(set-logic ALL)

(set-info :status unsat)

; forall a_bv:A. A(a_bv)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_bv () (Set Int))

(assert (set.subset a_bv UNIVERALSET))
(assert (>= (set.card a_bv) (- n t)))


(assert (not (>= (set.card a_bv) (- n t))))

(check-sat)
