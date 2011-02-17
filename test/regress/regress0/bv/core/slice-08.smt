(benchmark slice
  :status sat
  :logic QF_BV
  :extrafuns ((x BitVec[5]))
  :assumption (= (extract[4:3] x) (extract[1:0] x))
  :formula (not (= (extract[4:4] x) (extract[0:0] x)))
)
