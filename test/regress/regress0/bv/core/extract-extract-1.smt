(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[15:1] (extract[31:0] x)) (extract[15:1] x)))
)
