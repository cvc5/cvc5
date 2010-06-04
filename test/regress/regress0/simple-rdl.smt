(benchmark simple_rdl
  :logic QF_RDL
  :status unsat
  :extrafuns ((x Real) (y Real))
  :formula (not (implies (< (- x y) 0) (< x y)))
)
