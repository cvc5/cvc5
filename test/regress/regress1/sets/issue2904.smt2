(set-logic ALL_SUPPORTED)
(set-info :status unsat)
; conjecture set nonempty(~b & ~c)

(declare-fun n () Int)
(declare-fun f () Int)
(declare-fun m () Int)

(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (subset b UNIVERALSET))
(assert (subset c UNIVERALSET))

(assert (> n 0))
(assert (= (card UNIVERALSET) n))
(assert (= (card b) m))
(assert (= (card c) (- f m)))
(assert (>= m 0))
(assert (>= f m))
(assert (> n (+ (* 2 f) m)))


(assert (>= (card (setminus UNIVERALSET (intersection (setminus UNIVERALSET b) (setminus UNIVERALSET c)))) n))

(check-sat)
