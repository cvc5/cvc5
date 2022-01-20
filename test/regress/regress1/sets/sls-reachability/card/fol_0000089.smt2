(set-logic ALL)

(set-info :status unsat)

; forall b_du:B. forall a_dt:A. nonempty(b_du & a_dt & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_du () (Set Int))

(assert (set.subset b_du UNIVERALSET))
(assert (>= (* 2 (set.card b_du)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_dt () (Set Int))

(assert (set.subset a_dt UNIVERALSET))
(assert (>= (set.card a_dt) (- n t)))


(assert
  (= (set.card (set.inter (set.inter b_du a_dt) (set.minus UNIVERALSET f))) 0))

(check-sat)
