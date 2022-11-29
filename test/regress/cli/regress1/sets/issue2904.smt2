(set-logic ALL)
(set-info :status unsat)
; conjecture set nonempty(~b & ~c)

(declare-fun n () Int)
(declare-fun f () Int)
(declare-fun m () Int)

(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset b UNIVERALSET))
(assert (set.subset c UNIVERALSET))

(assert (> n 0))
(assert (= (set.card UNIVERALSET) n))
(assert (= (set.card b) m))
(assert (= (set.card c) (- f m)))
(assert (>= m 0))
(assert (>= f m))
(assert (> n (+ (* 2 f) m)))


(assert (>= (set.card (set.minus UNIVERALSET (set.inter (set.minus UNIVERALSET b) (set.minus UNIVERALSET c)))) n))

(check-sat)
