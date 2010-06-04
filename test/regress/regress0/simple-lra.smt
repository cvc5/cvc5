(benchmark simple_lra
  :logic QF_LRA
  :status unsat
  :extrafuns ((x Real) (y Real))
  :formula (not (implies (and (> x 0) (< (* 2 x) y)) (and (> y 0) (< x y))))
)
