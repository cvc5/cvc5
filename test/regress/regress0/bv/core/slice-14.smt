(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[16]))
  :assumption (= (extract[15:1] x) (extract[14:0] x))
  :assumption (= (extract[0:0] x) bv0[1])
  :formula (not (= x bv0[16]))
)
