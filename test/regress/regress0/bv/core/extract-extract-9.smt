(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[3:1] (extract[7:2] x)) (extract[5:3] x)))
)
