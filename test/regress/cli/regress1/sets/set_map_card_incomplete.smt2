; EXPECT: unknown
(set-logic HO_ALL)
; this problem is unsat, but the solver returns unknown for now
; because set.map and set.card are used together
;(set-info :status unsat)
(set-info :status unknown)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun f (Int) Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (distinct x1 x2))
(assert (set.member x1 A))
(assert (set.member x2 A))
(assert (= (f x1) (f x2)))
(assert (= B (set.map f A)))
(assert (= (set.card B) (set.card A)))

(check-sat)
