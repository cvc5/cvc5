(set-logic ALL)

(set-info :status unsat)

; forall a_bx:A. nonempty(a_bx & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_bx () (Set Int))

(assert (set.subset a_bx UNIVERALSET))
(assert (>= (set.card a_bx) (- n t)))


(assert (= (set.card (set.inter a_bx (set.minus UNIVERALSET f))) 0))

(check-sat)
