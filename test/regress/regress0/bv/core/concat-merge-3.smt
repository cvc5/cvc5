(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (extract[16:8] x) (extract[7:0] x)) (extract[16:0] x)))
)
