(benchmark simple_arr
  :logic QF_AX
  :status unsat
  :extrafuns ((a Array))
  :extrafuns ((i1 Index) (i2 Index))
  :formula (not (implies (= i1 i2) (= (select a i1) (select a i2))))
)
