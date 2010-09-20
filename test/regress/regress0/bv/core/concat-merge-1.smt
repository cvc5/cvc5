(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (extract[4:2] x) (extract[1:0] x)) (extract[4:0] x)))
)
