; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
; should instantiate f/x, g/y
(assert (forall ((x (-> U U U)) (y (-> U U))) (=> (not (= (x a) y)) (or (= (x a c) b) (= (y c) b)))))
(assert (not (= (f a c) b)))
(assert (not (= (g c) b)))
; this is required for unsatisfiable or else (f a) can be equal to g
(assert (not (= (f a a) (g a))))
(check-sat)
