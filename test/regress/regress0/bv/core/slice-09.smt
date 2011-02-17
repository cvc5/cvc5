(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[6]))
  :assumption (= (extract[5:2] x) (extract[3:0] x))
  :formula (not (= (extract[5:4] x) (extract[1:0] x)))
)
