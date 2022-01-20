(set-logic ALL)

(set-info :status unsat)

; forall b_gx:B. forall b_gw:B. forall a_gv:A. nonempty(b_gx & b_gw & a_gv)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_gx () (Set Int))

(assert (set.subset b_gx UNIVERALSET))
(assert (>= (* 2 (set.card b_gx)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gw () (Set Int))

(assert (set.subset b_gw UNIVERALSET))
(assert (>= (* 2 (set.card b_gw)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_gv () (Set Int))

(assert (set.subset a_gv UNIVERALSET))
(assert (>= (set.card a_gv) (- n t)))


(assert (= (set.card (set.inter (set.inter b_gx b_gw) a_gv)) 0))

(check-sat)
