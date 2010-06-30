(benchmark distinct_test
  :logic QF_UF
  :status unsat
  :extrafuns ((x U) (y U) (z U))
  :formula (not (iff (distinct x y z) (and (not (= x y)) (not (= x z)) (not (= y z))))))
