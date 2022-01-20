(set-logic ALL)

(set-info :status unsat)

; forall a_hf:A. forall a_he:A. nonempty(a_hf & a_he & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_hf () (Set Int))

(assert (set.subset a_hf UNIVERALSET))
(assert (>= (set.card a_hf) (- n t)))

(declare-fun a_he () (Set Int))

(assert (set.subset a_he UNIVERALSET))
(assert (>= (set.card a_he) (- n t)))


(assert
  (= (set.card (set.inter (set.inter a_hf a_he) (set.minus UNIVERALSET f))) 0))

(check-sat)
