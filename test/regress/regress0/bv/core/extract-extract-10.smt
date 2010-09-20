(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[2:2] (extract[7:2] x)) (extract[4:4] x)))
)
