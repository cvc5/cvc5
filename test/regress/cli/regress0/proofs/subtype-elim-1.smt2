; EXPECT: unsat
(set-option :simplification none)
(set-logic UFLRA)
(declare-fun f (Real) Real)
(declare-const y Real)
(declare-const x Real)
(assert (not (not (and (= (/ 1.0 2.0) (/ 1.0 2.0)) (and (<= x y) (and (<= y x) (distinct (f x) (f y))))))))
(check-sat)
