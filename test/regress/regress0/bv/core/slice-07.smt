(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[5]))
  :assumption (= (extract[4:1] x) (extract[3:0] x))
  :formula (not (= (extract[4:4] x) (extract[0:0] x)))
)
