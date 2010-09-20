(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[31:0] x) x))
)
