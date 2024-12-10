; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-const u U)
(declare-fun p (U U) Bool)
(assert (distinct
  (forall ((x U)) (or (p u x) (forall ((y U)) (p y x))))
  (forall ((x U) (y U)) (or (p u x) (p y x)))))
(check-sat)
