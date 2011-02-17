(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[16]))
  :assumption (= (extract[15:15] x) bv1[1])
  :assumption (= (extract[15:1] x) (extract[14:0] x))
  :formula (not (= x bv65535[16]))
)
