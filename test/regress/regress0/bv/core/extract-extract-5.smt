(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[7:1] (extract[15:1] x)) (extract[8:2] x)))
)
