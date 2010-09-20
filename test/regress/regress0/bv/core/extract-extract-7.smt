(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[3:3] (extract[15:1] x)) (extract[4:4] x)))
)
