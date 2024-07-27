; EXPECT: unsat
(set-logic ALL)

(declare-datatypes ((T1 0)(T2 0))
 (((cons1 (id1 Int) (tail1 T2)))
 ((Nil) (cons2 (id2 Int) (tail2 T1))))
)

(declare-const x T1)
(declare-const y T2)

(assert (= x (tail2 y)))
(assert (= y (tail1 x)))
(assert (not (= Nil y)))

(check-sat)
