(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (extract[2:1] x) (extract[0:0] x)) (extract[2:0] x)))
)
