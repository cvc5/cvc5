; EXPECT: false
(set-logic LRA)
(set-option :cegqi-nested-qe true)
(declare-const v2 Bool)
(declare-const r2 Real)
(get-qe (forall ((q0 Bool) (q1 Real) (q2 Bool)) (=> (or v2 q0) (distinct q1 q1 r2 r2 8817231.0))))
