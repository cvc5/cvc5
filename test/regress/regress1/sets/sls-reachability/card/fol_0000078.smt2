(set-logic ALL)

(set-info :status unsat)

; forall c_da:C. forall b_cz:B. forall a_cy:A. nonempty(c_da & b_cz & a_cy)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_da () (Set Int))

(assert (set.subset c_da UNIVERALSET))
(assert (>= (* 2 (set.card c_da)) (+ (- n t) 1)))

(declare-fun b_cz () (Set Int))

(assert (set.subset b_cz UNIVERALSET))
(assert (>= (* 2 (set.card b_cz)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_cy () (Set Int))

(assert (set.subset a_cy UNIVERALSET))
(assert (>= (set.card a_cy) (- n t)))


(assert (= (set.card (set.inter (set.inter c_da b_cz) a_cy)) 0))

(check-sat)
