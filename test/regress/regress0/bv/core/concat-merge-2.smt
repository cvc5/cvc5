(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (extract[8:4] x) (extract[3:0] x)) (extract[8:0] x)))
)
