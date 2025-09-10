; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-fun p (U U U) Bool)
(assert (distinct (forall ((x U) (y U) (z U)) (p x y z))
                  (forall ((z U) (y U) (x U)) (p x y z))))
(check-sat)
