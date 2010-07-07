(benchmark simple_arr
  :logic QF_AX
  :status unsat
  :extrafuns ((a Array))
  :extrafuns ((i1 Index) (i2 Index) (i3 Index))
  :formula (not (implies (and (= i1 i2) (= i2 i3)) (= (select a i1) (select a i3))))
)
