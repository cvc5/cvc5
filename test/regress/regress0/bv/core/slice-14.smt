(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[6]))
  :assumption (= (extract[5:1] x) (extract[4:0] x))
  :assumption (= (extract[0:0] x) bv0[1])
  :formula (not (= x bv0[6]))
)
