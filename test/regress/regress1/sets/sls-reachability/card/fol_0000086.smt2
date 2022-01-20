(set-logic ALL)

(set-info :status unsat)

; forall a_do:A. nonempty(a_do & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_do () (Set Int))

(assert (set.subset a_do UNIVERALSET))
(assert (>= (set.card a_do) (- n t)))


(assert (= (set.card (set.inter a_do (set.minus UNIVERALSET f))) 0))

(check-sat)
