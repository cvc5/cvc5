(set-logic ALL)

(set-info :status unsat)

; forall c_dz:C. forall a_dy:A. nonempty(c_dz & a_dy)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dz () (Set Int))

(assert (set.subset c_dz UNIVERALSET))
(assert (>= (* 2 (set.card c_dz)) (+ (- n t) 1)))

(declare-fun a_dy () (Set Int))

(assert (set.subset a_dy UNIVERALSET))
(assert (>= (set.card a_dy) (- n t)))


(assert (= (set.card (set.inter c_dz a_dy)) 0))

(check-sat)
