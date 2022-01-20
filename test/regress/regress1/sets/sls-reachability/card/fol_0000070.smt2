(set-logic ALL)

(set-info :status unsat)

; forall c_ch:C. forall b_cg:B. nonempty(c_ch & b_cg & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_ch () (Set Int))

(assert (set.subset c_ch UNIVERALSET))
(assert (>= (* 2 (set.card c_ch)) (+ (- n t) 1)))

(declare-fun b_cg () (Set Int))

(assert (set.subset b_cg UNIVERALSET))
(assert (>= (* 2 (set.card b_cg)) (+ (+ n (* 3 t)) 1)))


(assert
  (= (set.card (set.inter (set.inter c_ch b_cg) (set.minus UNIVERALSET f))) 0))

(check-sat)
