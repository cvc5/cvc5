(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[8]))
  :assumption (= (extract[3:0] x) bv0[4])
  :assumption (= (extract[7:4] x) bv15[4])
  :formula (not (= x bv240[8]))
)
